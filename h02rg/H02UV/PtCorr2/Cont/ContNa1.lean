import PtCorr2.Last.LastAB3
import PtCorr2.Pair.PairReduce

set_option autoImplicit false

/-!
# The `σ_a` part of the last step for a general observable state (model level)

The one-point analogues of `finG_jets_ab` and `lastDef_ab_le`, for inputs **with** one-point parts
(no `abSub`, locality `CmpIn` of the three components `∅, a, b`), at the last scale `j + 1 = N`:

* **`na_finG_jets_a`**: with `σ_a` sizes `‖V(B)_a‖ ≤ M_V ≤ M`, `‖𝒲(B)_a‖ ≤ m_W ≤ τM`,
  `A^{(|𝓑_j(X)|-4)_+}‖K(X)_a‖ ≤ τM/r₀` (weight `wA`):
  `ℓ'²|c2(F_N)_a| ≤ c_J(c_ρ + 4/r₀²)τM + L²((Q₁ + 2L²Q₁²)M_V + Q₁m_W)`,
  `|ε(F_N)_a| ≤ c_J(c_ρ + 4/r₀²)τM`
  (`LastJetBd` directly, plus the crude bound of `∑_Bc2(V_N(B))_a` as in `finG_jets_ab`);
* **`na_eps_uXO_a_le`**: the `σ_a` constant of the last step,
  `|ε(u^{obs}_N(Λ))_a| = |∑_Bε(V'_B)_a − ∑_Bε(S(B))_a| ≤ L²((Q₁ + 2L²Q₁²)M + Q₁m_W)`
  (no activity term at the last scale; `eps_total_LS`; `Vpr_oA`, `Sb_oA`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Obs.Gen

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 4000000 in
/-- **The `σ_a` jets of `F_N` at the last scale for general inputs.** -/
theorem na_finG_jets_a {A r₀ : ℝ} (hJ : LastJetBd L A r₀) (hA1 : 1 ≤ A) (_hr₀ : 0 < r₀)
    (hr₀1 : r₀ ≤ 1) :
    ∀ (N j : ℕ), j + 1 = N → pauliL0 2 ≤ L → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC →
      ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ, Step2.GoodCov2 j ℓC C →
    ∀ (P : ObsPts 2 L N) (V W : OFam .two 2 L N) (K : OAct .two 2 L N),
      Step2.InF j (bulkF V) → Step2.InF j (bulkF W) →
      (∀ b, ε ((bulkF V b : EvR (Lam 2 L N)) : Alg 2 L N) = 0) → Step2.InK2 j (bulkF K) →
      (∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
        (V b : SA .two (Lam 2 L N))) →
      (∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
        (W b : SA .two (Lam 2 L N))) →
      (∀ X, IsConn j X → CmpIn (nbhd j X : Set (Lam 2 L N)) (K X : SA .two (Lam 2 L N))) →
      ∀ τ M MV mW : ℝ, 0 < τ → τ ≤ r₀ → 0 < M → 0 ≤ MV → MV ≤ M → 0 ≤ mW → mW ≤ τ * M →
      Step2.Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal τ →
      Step2.Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal τ →
      Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal τ →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (V b) ≤ ENNReal.ofReal MV) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (W b) ≤ ENNReal.ofReal mW) →
      (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) * oTo Obs2.wA j ℓ (K X) ≤
        ENNReal.ofReal (τ * M / r₀)) →
      cRho L * τ ≤ 1 → 4 * τ ≤ r₀ ^ 2 →
        ℓ' ^ 2 * ‖Suscept.c2 ((finG P j C V W K : SA .two (Lam 2 L N)).a)‖ ≤
          cJet L * (cRho L + 4 / r₀ ^ 2) * τ * M +
            (L : ℝ) ^ 2 * ((Step2.Q1 2 + 2 * (L : ℝ) ^ 2 * Step2.Q1 2 ^ 2) * MV +
              Step2.Q1 2 * mW) ∧
        ‖ε ((finG P j C V W K : SA .two (Lam 2 L N)).a)‖ ≤
          cJet L * (cRho L + 4 / r₀ ^ 2) * τ * M := by
  intro N j hj hLp ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC P V W K hV hW hV0 hK hVl hWl hKl
    τ M MV mW hτ hτr hM hMV0 hMVM hmW0 hmW hVb hWb hKb hVoV hWo hKo hsm hsm2
  have hτ1 : τ ≤ 1 := hτr.trans hr₀1
  have hVo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (V b) ≤ ENNReal.ofReal M :=
    fun b hb => (hVoV b hb).trans (ENNReal.ofReal_le_ofReal hMVM)
  obtain ⟨h1, h2⟩ := hJ N j hj hLp ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC P V W K hV hW hV0 hK hVl hWl hKl
    τ M mW hτ hτr hM hmW0 hmW hVb hWb hKb hVo hWo hKo hsm hsm2
  refine ⟨?_, h2⟩
  have hVr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j ℓ ((bulkF V b : EvR (Lam 2 L N)) : Alg 2 L N) ≤ ENNReal.ofReal τ :=
    fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj 2 (L : ℝ) j ℓ ((bulkF V b : EvR (Lam 2 L N)) : Alg 2 L N)) b hb).trans hVb
  have hWr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j ℓ ((bulkF W b : EvR (Lam 2 L N)) : Alg 2 L N) ≤ ENNReal.ofReal τ :=
    fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj 2 (L : ℝ) j ℓ ((bulkF W b : EvR (Lam 2 L N)) : Alg 2 L N)) b hb).trans hWb
  have H : Step2.LastN.BHN j ℓ ℓ' ℓC C (bulkF V) (bulkF W) (bulkF K) A τ :=
    { hd := le_refl _ |>.trans (by norm_num), hLp := hLp, hjN := hj, hℓ := hℓ, hℓ' := hℓ',
      hℓC := hℓC, hsum := hsum, hC := hC, hV := hV, hW := hW, hV0 := hV0, hK := hK, hA := hA1,
      hr := hτ.le, hr1 := hτ1, hVr := hVr', hWr := hWr', hKr := hKb }
  have hQ := H.hQ1
  have hQ0 : 0 ≤ Step2.Q1 2 := by linarith
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hn : ((blockIdx (d := 2) (L := L) (N := N) j).card : ℝ) ≤ (L : ℝ) ^ 2 := by
    exact_mod_cast Step2.LastN.card_blockIdx_last (d := 2) (L := L) hj
  have hVp : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ℓ' ^ 2 * ‖Suscept.c2 ((VprO C V b : SA .two (Lam 2 L N)).a)‖ ≤ Step2.Q1 2 * MV :=
    fun b hb => c2_le_of_Tj hℓ' (mul_nonneg hQ0 hMV0) (by
      rw [← Obs2.oTo_wA]
      exact Vpr_oA H hVl hVoV hb)
  have hSb : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ℓ' ^ 2 * ‖Suscept.c2 ((SbO j C V W b : SA .two (Lam 2 L N)).a)‖ ≤
        (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * MV) + Step2.Q1 2 * mW :=
    fun b hb => c2_le_of_Tj hℓ' (add_nonneg (by positivity) (mul_nonneg hQ0 hmW0)) (by
      rw [← Obs2.oTo_wA]
      exact Sb_oA H hVl hWl hMV0 hmW0 hVoV hWo hb)
  have hLS : ∑ b ∈ blockIdx (L := L) (N := N) j,
      Suscept.c2 ((LSO P j C V W b : SA .two (Lam 2 L N)).a) =
      ∑ b ∈ blockIdx (L := L) (N := N) j,
        Suscept.c2 ((SbO j C V W b : SA .two (Lam 2 L N)).a) := by
    have h := total_W_mass P j C V W mass2L (locMass_two P.a)
    have e : ∀ b, mass2L ((WpO P j C V W b : SA .two (Lam 2 L N)).a) =
        -(Suscept.c2 ((SbO j C V W b : SA .two (Lam 2 L N)).a) -
          Suscept.c2 ((LSO P j C V W b : SA .two (Lam 2 L N)).a)) := fun b => by
      show mass2 _ = _
      rw [mass2_eq_neg_c2]
      congr 1
      exact PtCorr.c2_sub _ _
    rw [sum_congr rfl fun b _ => e b, sum_neg_distrib, neg_eq_zero, sum_sub_distrib,
      sub_eq_zero] at h
    exact h.symm
  have hsum' : ∑ b ∈ blockIdx (L := L) (N := N) j,
      Suscept.c2 ((VpO P j C V W K b : SA .two (Lam 2 L N)).a) =
      ∑ b ∈ blockIdx (L := L) (N := N) j, Suscept.c2 ((VprO C V b : SA .two (Lam 2 L N)).a) -
        ∑ b ∈ blockIdx (L := L) (N := N) j,
          Suscept.c2 ((SbO j C V W b : SA .two (Lam 2 L N)).a) := by
    rw [sum_congr rfl fun b _ => c2_VpO_a_last P j C V W K hj b, sum_sub_distrib, hLS]
  set X := ∑ b ∈ blockIdx (L := L) (N := N) j,
    Suscept.c2 ((VpO P j C V W K b : SA .two (Lam 2 L N)).a) with hXd
  have hX : ℓ' ^ 2 * ‖X‖ ≤
      (L : ℝ) ^ 2 * ((Step2.Q1 2 + 2 * (L : ℝ) ^ 2 * Step2.Q1 2 ^ 2) * MV + Step2.Q1 2 * mW) := by
    rw [hsum']
    have hA' := norm_sum_le (blockIdx (L := L) (N := N) j)
      fun b => Suscept.c2 ((VprO C V b : SA .two (Lam 2 L N)).a)
    have hB' := norm_sum_le (blockIdx (L := L) (N := N) j)
      fun b => Suscept.c2 ((SbO j C V W b : SA .two (Lam 2 L N)).a)
    have hℓ2 : 0 ≤ ℓ' ^ 2 := sq_nonneg _
    have k1 : ℓ' ^ 2 * ∑ b ∈ blockIdx (L := L) (N := N) j,
        ‖Suscept.c2 ((VprO C V b : SA .two (Lam 2 L N)).a)‖ ≤ (L : ℝ) ^ 2 * (Step2.Q1 2 * MV) := by
      rw [mul_sum]
      refine (sum_le_card_nsmul _ _ _ hVp).trans ?_
      rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hn (mul_nonneg hQ0 hMV0)
    have hSbt : (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * MV) + Step2.Q1 2 * mW ≤
        (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * MV + Step2.Q1 2 * mW := by
      have e1 : τ * MV ≤ MV := mul_le_of_le_one_left hMV0 hτ1
      have := mul_le_mul_of_nonneg_left e1
        (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2))
      linarith
    have hS0 : 0 ≤ (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * MV + Step2.Q1 2 * mW :=
      add_nonneg (mul_nonneg (mul_nonneg hL2 (mul_nonneg zero_le_two (sq_nonneg _))) hMV0)
        (mul_nonneg hQ0 hmW0)
    have k2 : ℓ' ^ 2 * ∑ b ∈ blockIdx (L := L) (N := N) j,
        ‖Suscept.c2 ((SbO j C V W b : SA .two (Lam 2 L N)).a)‖ ≤
        (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * MV + Step2.Q1 2 * mW) := by
      rw [mul_sum]
      refine (sum_le_card_nsmul _ _ _ fun b hb => (hSb b hb).trans hSbt).trans ?_
      rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hn hS0
    calc ℓ' ^ 2 * ‖∑ b ∈ blockIdx (L := L) (N := N) j,
            Suscept.c2 ((VprO C V b : SA .two (Lam 2 L N)).a) -
          ∑ b ∈ blockIdx (L := L) (N := N) j,
            Suscept.c2 ((SbO j C V W b : SA .two (Lam 2 L N)).a)‖
        ≤ ℓ' ^ 2 * (∑ b ∈ blockIdx (L := L) (N := N) j,
            ‖Suscept.c2 ((VprO C V b : SA .two (Lam 2 L N)).a)‖ +
          ∑ b ∈ blockIdx (L := L) (N := N) j,
            ‖Suscept.c2 ((SbO j C V W b : SA .two (Lam 2 L N)).a)‖) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hA' hB')) hℓ2
      _ ≤ (L : ℝ) ^ 2 * (Step2.Q1 2 * MV) +
          (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * MV + Step2.Q1 2 * mW) := by
          rw [mul_add]; exact add_le_add k1 k2
      _ = _ := by ring
  have hℓ2 : 0 ≤ ℓ' ^ 2 := sq_nonneg _
  have := norm_sub_le (Suscept.c2 ((finG P j C V W K : SA .two (Lam 2 L N)).a) + X) X
  rw [add_sub_cancel_right] at this
  calc ℓ' ^ 2 * ‖Suscept.c2 ((finG P j C V W K : SA .two (Lam 2 L N)).a)‖
      ≤ ℓ' ^ 2 * ‖Suscept.c2 ((finG P j C V W K : SA .two (Lam 2 L N)).a) + X‖ + ℓ' ^ 2 * ‖X‖ := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left this hℓ2
    _ ≤ _ := add_le_add h1 hX

section Model

variable (P : ObsPts 2 L N) (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ)
  (V W : OFam .two 2 L N) (K : OAct .two 2 L N)

/-- The `σ_a` constant of the last step: `ε(u^{obs}_N(Λ))_a = ∑_Bε(V'_B)_a − ∑_Bε(S(B))_a`. -/
theorem na_eps_uXO_a_last (hj : j + 1 = N) :
    ε (uXO P j C V W K univ : SA .two (Lam 2 L N)).a =
      ∑ b ∈ blockIdx (L := L) (N := N) j, ε (VprO C V b : SA .two (Lam 2 L N)).a -
        ∑ b ∈ blockIdx (L := L) (N := N) j, ε (SbO j C V W b : SA .two (Lam 2 L N)).a := by
  have hu : (uXO P j C V W K univ : SA .two (Lam 2 L N)).a =
      ∑ b ∈ blockIdx (L := L) (N := N) j, (upO P j C V W K b : SA .two (Lam 2 L N)).a := by
    rw [uXO, AddSubmonoidClass.coe_finsetSum, sum_a]; rfl
  have hb : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ε (upO P j C V W K b : SA .two (Lam 2 L N)).a =
      ε (VprO C V b : SA .two (Lam 2 L N)).a -
        ε (locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) j b)
            (blockSet (L := L) (N := N) j b)
            (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam 2 L N)).a) := by
    intro b _
    have hQ : (Q2O P j K b : SA .two (Lam 2 L N)).a = 0 := by rw [Q2O_last P hj]; rfl
    have hV : (VprO C V b : SA .two (Lam 2 L N)).a = expLC C (V b : SA .two (Lam 2 L N)).a := by
      rw [VprO, EthO_eq_expO, coe_expO, expS_a]
    rw [upO_a, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, uVpO_a, hQ,
      map_zero, sub_zero, map_sub, hV]
  rw [hu, map_sum, sum_congr rfl hb, sum_sub_distrib, eps_total_LS]

set_option maxHeartbeats 2000000 in
/-- **The `σ_a` constant of the last step, bounded** (general inputs). -/
theorem na_eps_uXO_a_le (hj : j + 1 = N) (hLp : pauliL0 2 ≤ L) {A : ℝ} (hA1 : 1 ≤ A)
    {ℓ ℓ' ℓC : ℝ} (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (hℓC : 0 < ℓC) (hsum : ℓ' + ℓC ≤ 2 * ℓ)
    (hC : Step2.GoodCov2 j ℓC C)
    (hV : Step2.InF j (bulkF V)) (hW : Step2.InF j (bulkF W))
    (hV0 : ∀ b, ε ((bulkF V b : EvR (Lam 2 L N)) : Alg 2 L N) = 0) (hK : Step2.InK2 j (bulkF K))
    (hVl : ∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
      (V b : SA .two (Lam 2 L N)))
    (hWl : ∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
      (W b : SA .two (Lam 2 L N)))
    {τ M mW : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hM : 0 ≤ M) (hmW0 : 0 ≤ mW)
    (hVb : Step2.Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal τ)
    (hWb : Step2.Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal τ)
    (hKb : Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal τ)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (V b) ≤ ENNReal.ofReal M)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (W b) ≤ ENNReal.ofReal mW) :
    ‖ε (uXO P j C V W K univ : SA .two (Lam 2 L N)).a‖ ≤
      (L : ℝ) ^ 2 * ((Step2.Q1 2 + 2 * (L : ℝ) ^ 2 * Step2.Q1 2 ^ 2) * M + Step2.Q1 2 * mW) := by
  have hVr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j ℓ ((bulkF V b : EvR (Lam 2 L N)) : Alg 2 L N) ≤ ENNReal.ofReal τ :=
    fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj 2 (L : ℝ) j ℓ ((bulkF V b : EvR (Lam 2 L N)) : Alg 2 L N)) b hb).trans hVb
  have hWr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j ℓ ((bulkF W b : EvR (Lam 2 L N)) : Alg 2 L N) ≤ ENNReal.ofReal τ :=
    fun b hb => (le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj 2 (L : ℝ) j ℓ ((bulkF W b : EvR (Lam 2 L N)) : Alg 2 L N)) b hb).trans hWb
  have H : Step2.LastN.BHN j ℓ ℓ' ℓC C (bulkF V) (bulkF W) (bulkF K) A τ :=
    { hd := le_refl _ |>.trans (by norm_num), hLp := hLp, hjN := hj, hℓ := hℓ, hℓ' := hℓ',
      hℓC := hℓC, hsum := hsum, hC := hC, hV := hV, hW := hW, hV0 := hV0, hK := hK, hA := hA1,
      hr := hτ.le, hr1 := hτ1, hVr := hVr', hWr := hWr', hKr := hKb }
  have hQ := H.hQ1
  have hQ0 : 0 ≤ Step2.Q1 2 := by linarith
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hn : ((blockIdx (d := 2) (L := L) (N := N) j).card : ℝ) ≤ (L : ℝ) ^ 2 := by
    exact_mod_cast Step2.LastN.card_blockIdx_last (d := 2) (L := L) hj
  have hVp : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ‖ε ((VprO C V b : SA .two (Lam 2 L N)).a)‖ ≤ Step2.Q1 2 * M :=
    fun b hb => eps_le_of_Tj hℓ' (mul_nonneg hQ0 hM) (by
      rw [← Obs2.oTo_wA]
      exact Vpr_oA H hVl hVo hb)
  have hSb : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ‖ε ((SbO j C V W b : SA .two (Lam 2 L N)).a)‖ ≤
        (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * M) + Step2.Q1 2 * mW :=
    fun b hb => eps_le_of_Tj hℓ' (add_nonneg (by positivity) (mul_nonneg hQ0 hmW0)) (by
      rw [← Obs2.oTo_wA]
      exact Sb_oA H hVl hWl hM hmW0 hVo hWo hb)
  have hSbt : (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * M) + Step2.Q1 2 * mW ≤
      (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * M + Step2.Q1 2 * mW := by
    have e1 : τ * M ≤ M := mul_le_of_le_one_left hM hτ1
    have := mul_le_mul_of_nonneg_left e1
      (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2))
    linarith
  have hS0 : 0 ≤ (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * M + Step2.Q1 2 * mW :=
    add_nonneg (mul_nonneg (mul_nonneg hL2 (mul_nonneg zero_le_two (sq_nonneg _))) hM)
      (mul_nonneg hQ0 hmW0)
  have k1 : ‖∑ b ∈ blockIdx (L := L) (N := N) j, ε ((VprO C V b : SA .two (Lam 2 L N)).a)‖ ≤
      (L : ℝ) ^ 2 * (Step2.Q1 2 * M) := by
    refine (norm_sum_le _ _).trans ((sum_le_card_nsmul _ _ _ hVp).trans ?_)
    rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hn (mul_nonneg hQ0 hM)
  have k2 : ‖∑ b ∈ blockIdx (L := L) (N := N) j, ε ((SbO j C V W b : SA .two (Lam 2 L N)).a)‖ ≤
      (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * M + Step2.Q1 2 * mW) := by
    refine (norm_sum_le _ _).trans ((sum_le_card_nsmul _ _ _ fun b hb =>
      (hSb b hb).trans hSbt).trans ?_)
    rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hn hS0
  rw [na_eps_uXO_a_last P j C V W K hj]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ (L : ℝ) ^ 2 * (Step2.Q1 2 * M) +
        (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * M + Step2.Q1 2 * mW) :=
        add_le_add k1 k2
    _ = _ := by ring

end Model

/-! ### `n_a` of the last factor of a general state -/

section Split

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- `s_a(r·e^x e^{−U}) = s_∅(r·e^x e^{−U})·(−ε(U_a))` for an observable constant `U`. -/
theorem na_sA_smul_expU_neg (r x : ℂ) {U : OE .two Λ} (hU : bulk U = 0) :
    sA (r • expU x (-U)) = sE (r • expU x (-U)) * -ε (U : SA .two Λ).a := by
  have hb : bulk (-U) = 0 := by rw [map_neg, hU, neg_zero]
  rw [sE_smul_expU r x hb]
  unfold sA expU
  simp only [SetLike.val_smul, SA.smul_a, map_smul, smul_eq_mul]
  rw [oexp_obs_a hb, NegMemClass.coe_neg, SA.neg_a, map_neg]
  ring

end Split

end

end PtCorr2
