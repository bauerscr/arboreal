import PtCorr2.Last.LastObsK4
import PtCorr2.Last.LastObsA

/-!
# The `σ_a` jets of `F_N` from norm bounds of the inputs of the last step (model level)

**`finG_jets_le`**: at `j + 1 = N`, for inputs with bulk sizes `≤ τ` (`‖V^∅‖_j, ‖𝒲^∅‖_j,
‖K^∅‖_{j,A} ≤ τ`), observable sizes `‖V^{obs}(B)‖ ≤ M`, `‖𝒲^{obs}(B)‖ ≤ m_W ≤ τM` and
`A^{(|𝓑_j(X)|-4)_+}‖K^{obs}(X)‖ ≤ τM/r₀` (weight `w_a = 1`), `τ ≤ r₀` and the smallness
`c_ρ(L)τ ≤ 1`, `4τ ≤ r₀²`:

  `|c2(F_N)_a + ∑_Bc2V_N(B)_a| ≤ c_J (c_ρ + 4/r₀²) τ M / ℓ'²`,
  `|ε(F_N)_a| ≤ c_J (c_ρ + 4/r₀²) τ M`,

`c_J = 60(1 + L²Q₁)`, `c_ρ = L²(2c_S^N + 4L²Q₁² + 4Q₁ + L²c_S^N)`. The bound of `K'(Λ)` is
`PtCorr2.KNO_a_le`; the other inputs are the block bounds of the last step (no localisation is
needed: `Loc_{Λ,B}` enters only through `ε(Loc_{Λ,B}S(Λ))_∅ = ε S(Λ)_∅|B|/|Λ|`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Obs.Gen TrivSqZeroExt

variable {L N : ℕ} [NeZero L]

/-- The jet norm from the two component norms. -/
theorem nw_JT_le {k : ℕ} {ℓ β a b : ℝ} (hℓ : 0 < ℓ) (hβ : 0 ≤ β) (F : OE .two (Lam 2 L N))
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : Tj 2 (L : ℝ) k ℓ (F : SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal a)
    (h2 : Tj 2 (L : ℝ) k ℓ (F : SA .two (Lam 2 L N)).a ≤ ENNReal.ofReal b) :
    nw (ℓ ^ 2) β (JT F) ≤ 2 * a + 2 * β * b := by
  have hh : (0 : ℝ) < (L : ℝ) ^ k := Lpow_pos k
  have hε : ∀ x : Alg 2 L N, ∀ c : ℝ, 0 ≤ c → Tj 2 (L : ℝ) k ℓ x ≤ ENNReal.ofReal c →
      ‖ε x‖ ≤ c ∧ ℓ ^ 2 * ‖Suscept.c2 x‖ ≤ c := fun x c hc hx => by
    have hfin : Tj 2 (L : ℝ) k ℓ x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
    have hT : (Tj 2 (L : ℝ) k ℓ x).toReal ≤ c := ENNReal.toReal_le_of_le_ofReal hc hx
    refine ⟨?_, ?_⟩
    · have := (abs_ε_le (E := Dir 2) (p := pPhi 2) hh hℓ x).trans hx
      exact (ENNReal.ofReal_le_ofReal_iff hc).1 this
    · have h := Suscept.norm_c2_le (E := Dir 2) (p := pPhi 2) hh hℓ x
      have hℓ2 : 0 < ℓ ^ 2 := by positivity
      calc ℓ ^ 2 * ‖Suscept.c2 x‖ ≤ ℓ ^ 2 * ((Tj 2 (L : ℝ) k ℓ x).toReal * ℓ⁻¹ ^ 2) :=
            mul_le_mul_of_nonneg_left h hℓ2.le
        _ = (Tj 2 (L : ℝ) k ℓ x).toReal := by field_simp
        _ ≤ c := hT
  obtain ⟨e1, e2⟩ := hε _ a ha h1
  obtain ⟨e3, e4⟩ := hε _ b hb h2
  unfold nw
  rw [JT_eps_e, JT_c2_e, JT_eps_a, JT_c2_a]
  have := mul_le_mul_of_nonneg_left e3 hβ
  have := mul_le_mul_of_nonneg_left e4 hβ
  nlinarith

section Sizes

variable {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}
  {V W : OFam .two 2 L N} {K : OAct .two 2 L N} {A τ : ℝ}
  (H : Step2.LastN.BHN j ℓ ℓ' ℓC C (bulkF V) (bulkF W) (bulkF K) A τ)
include H

theorem V2_oA (hVl : ∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
      (V b : SA .two (Lam 2 L N))) {M : ℝ}
    (hVm : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (V b) ≤ ENNReal.ofReal M)
    {b : Fin 2 → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo Obs2.wA (j + 1) (2 * ℓ) (V b) ≤ ENNReal.ofReal (Step2.Q1 2 * M) := by
  refine (oTj_succ_two_le Obs2.wA_ab H.hd H.hLp H.hj (hVl b).πobs H.hℓ).trans ?_
  exact le_ofReal_mul (by linarith [H.hQ1])
    (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hd H.hj.le b)) (hVm b hb)

theorem Vpr_oA (hVl : ∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
      (V b : SA .two (Lam 2 L N))) {M : ℝ}
    (hVm : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (V b) ≤ ENNReal.ofReal M)
    {b : Fin 2 → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo Obs2.wA (j + 1) ℓ' (VprO C V b) ≤ ENNReal.ofReal (Step2.Q1 2 * M) := by
  rw [VprO]
  refine (oTo_EthO_le2 Obs2.wA_ab H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (hVl b)).trans ?_
  exact le_ofReal_mul (by linarith [H.hQ1])
    (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hd H.hj.le b)) (hVm b hb)

theorem Sb_oA (hVl : ∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
      (V b : SA .two (Lam 2 L N)))
    (hWl : ∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N))
      (W b : SA .two (Lam 2 L N))) {M mW : ℝ} (hM : 0 ≤ M) (hmW : 0 ≤ mW)
    (hVm : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (V b) ≤ ENNReal.ofReal M)
    (hWm : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (W b) ≤ ENNReal.ofReal mW)
    {b : Fin 2 → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo Obs2.wA (j + 1) ℓ' (SbO j C V W b) ≤
      ENNReal.ofReal ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * M) + Step2.Q1 2 * mW) := by
  have hQ := H.hQ1
  have hτ := H.hr
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hpair : ∀ b' ∈ blockIdx (L := L) (N := N) j,
      oTo Obs2.wA (j + 1) ℓ' (FCO C (EthO C (πobs (V b)))
        (EthO C (emb (bulk (V b')) : OE .two (Lam 2 L N)))) ≤
        ENNReal.ofReal (2 * Step2.Q1 2 ^ 2 * (τ * M)) := fun b' hb' => by
    refine (oTo_le _ _ _ _).trans ((oTj_FCO_le H.hℓ' H.hℓC H.hsum H.hC Obs2.wA_sub _ _).trans ?_)
    have e : 2 * Step2.Q1 2 ^ 2 * (τ * M) = 2 * ((Step2.Q1 2 * M) * (Step2.Q1 2 * τ)) := by ring
    rw [e, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    refine mul_le_mul_right (le_ofReal_mul (mul_nonneg (by linarith) hM) (V2_oA H hVl hVm hb) ?_) _
    rw [oTj_emb]; exact H.V2_le hb'
  have hSF : oTo Obs2.wA (j + 1) ℓ' (SFO j C V b) ≤
      ENNReal.ofReal ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * M)) := by
    rw [BHO.oTo_SFO_eq Obs2.wA_ab]
    refine (oTo_sum_le _ _ _ _ _).trans ?_
    refine (le_ofReal_sum_const _ (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg _))
      (mul_nonneg hτ hM)) hpair).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : ((blockIdx (d := 2) (L := L) (N := N) j).card : ℝ) ≤ (L : ℝ) ^ 2 := by
      exact_mod_cast Step2.LastN.card_blockIdx_last (d := 2) (L := L) H.hjN
    calc ((blockIdx (L := L) (N := N) j).card : ℝ) * (2 * Step2.Q1 2 ^ 2 * (τ * M))
        ≤ (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2 * (τ * M)) := by gcongr
      _ = _ := by ring
  have hEW : oTo Obs2.wA (j + 1) ℓ' (EthO C (W b)) ≤ ENNReal.ofReal (Step2.Q1 2 * mW) := by
    refine (oTo_EthO_le2 Obs2.wA_ab H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (hWl b)).trans ?_
    exact le_ofReal_mul (by linarith)
      (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hd H.hj.le b)) (hWm b hb)
  rw [SbO]
  have h0 : 0 ≤ (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * M) :=
    mul_nonneg (mul_nonneg hL2 (mul_nonneg zero_le_two (sq_nonneg _))) (mul_nonneg hτ hM)
  exact (oTo_add_le _ _ _ _ _).trans (le_ofReal_add h0 (mul_nonneg (by linarith) hmW) hSF hEW)

end Sizes

/-- `c_ρ(L)`. -/
def cRho (L : ℕ) : ℝ :=
  (L : ℝ) ^ 2 * (2 * Step2.LastN.cSN 2 L + 4 * (L : ℝ) ^ 2 * Step2.Q1 2 ^ 2 + 4 * Step2.Q1 2 +
    (L : ℝ) ^ 2 * Step2.LastN.cSN 2 L)

/-- `c_J(L) = 60(1 + L²Q₁)`. -/
def cJet (L : ℕ) : ℝ := 60 * (1 + (L : ℝ) ^ 2 * Step2.Q1 2)

theorem c2_le_of_Tj {k : ℕ} {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 ≤ c) {x : Alg 2 L N}
    (hx : Tj 2 (L : ℝ) k ℓ x ≤ ENNReal.ofReal c) : ℓ ^ 2 * ‖Suscept.c2 x‖ ≤ c := by
  have hh : (0 : ℝ) < (L : ℝ) ^ k := Lpow_pos k
  have hT : (Tj 2 (L : ℝ) k ℓ x).toReal ≤ c := ENNReal.toReal_le_of_le_ofReal hc hx
  have h := Suscept.norm_c2_le (E := Dir 2) (p := pPhi 2) hh hℓ x
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  calc ℓ ^ 2 * ‖Suscept.c2 x‖ ≤ ℓ ^ 2 * ((Tj 2 (L : ℝ) k ℓ x).toReal * ℓ⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left h hℓ2.le
    _ = (Tj 2 (L : ℝ) k ℓ x).toReal := by field_simp
    _ ≤ c := hT

theorem eps_le_of_Tj {k : ℕ} {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 ≤ c) {x : Alg 2 L N}
    (hx : Tj 2 (L : ℝ) k ℓ x ≤ ENNReal.ofReal c) : ‖ε x‖ ≤ c := by
  have hh : (0 : ℝ) < (L : ℝ) ^ k := Lpow_pos k
  exact (ENNReal.ofReal_le_ofReal_iff hc).1 ((abs_ε_le (E := Dir 2) (p := pPhi 2) hh hℓ x).trans hx)

/-- **The jet bound of the last step** at regulator `A` and radius `r₀` (the conclusion of
`finG_jets_le`). -/
def LastJetBd (L : ℕ) [NeZero L] (A r₀ : ℝ) : Prop :=
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
      ∀ τ M mW : ℝ, 0 < τ → τ ≤ r₀ → 0 < M → 0 ≤ mW → mW ≤ τ * M →
      Step2.Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal τ →
      Step2.Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal τ →
      Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal τ →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (V b) ≤ ENNReal.ofReal M) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo Obs2.wA j ℓ (W b) ≤ ENNReal.ofReal mW) →
      (∀ X, IsConn j X → ENNReal.ofReal (A ^ (nb j X - 2 ^ 2)) * oTo Obs2.wA j ℓ (K X) ≤
        ENNReal.ofReal (τ * M / r₀)) →
      cRho L * τ ≤ 1 → 4 * τ ≤ r₀ ^ 2 →
        ℓ' ^ 2 * ‖Suscept.c2 ((finG P j C V W K : SA .two (Lam 2 L N)).a) +
          ∑ b ∈ blockIdx (L := L) (N := N) j,
            Suscept.c2 ((VpO P j C V W K b : SA .two (Lam 2 L N)).a)‖ ≤
          cJet L * (cRho L + 4 / r₀ ^ 2) * τ * M ∧
        ‖ε ((finG P j C V W K : SA .two (Lam 2 L N)).a)‖ ≤
          cJet L * (cRho L + 4 / r₀ ^ 2) * τ * M

set_option maxHeartbeats 4000000 in
/-- **The `σ_a` jets of `F_N` at the last scale from norm bounds of the inputs.** -/
theorem finG_jets_le : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ LastJetBd L A r₀ := by
  obtain ⟨L₀, h0⟩ := KNO_a_le
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h1⟩ := h0 L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨r₀, hr₀, hr₀1, hK'⟩ := h1 A hA
  refine ⟨r₀, hr₀, hr₀1, ?_⟩
  intro N j hj hLp ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC P V W K hV hW hV0 hK hVl hWl hKl τ M mW hτ hτr hM
    hmW0 hmW hVb hWb hKb hVo hWo hKo hsm hsm2
  have hτ1 : τ ≤ 1 := hτr.trans hr₀1
  have hmWM : mW ≤ M := hmW.trans (mul_le_of_le_one_left hM.le hτ1)
  obtain ⟨hKa, hKe⟩ := hK' N j hj ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC V W K hV hW hV0 hK hVl hWl hKl
    τ M hτ hτr hM hVb hWb hKb hVo (fun b hb => (hWo b hb).trans (ENNReal.ofReal_le_ofReal hmWM)) hKo
  have hA1 : 1 ≤ A := hA₀.trans hA
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
  have hcS := H.hcS
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hn : ((blockIdx (d := 2) (L := L) (N := N) j).card : ℝ) ≤ (L : ℝ) ^ 2 := by
    exact_mod_cast Step2.LastN.card_blockIdx_last (d := 2) (L := L) hj
  set β := 1 / M with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβM : β * M = 1 := by rw [hβ]; field_simp
  set ρ := cRho L * τ with hρ
  set κ := 4 * τ / r₀ ^ 2 with hκ
  -- block bounds
  have hSe : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) (j + 1) ℓ' ((SbO j C V W b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e ≤
        ENNReal.ofReal (Step2.LastN.cSN 2 L * τ) := fun b hb => by
    show Tj 2 (L : ℝ) (j + 1) ℓ' ((bulk (SbO j C V W b) : EvR (Lam 2 L N)) : Alg 2 L N) ≤ _
    rw [bulk_SbO]; exact H.Sb_le hb
  have hSa : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) (j + 1) ℓ' ((SbO j C V W b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a ≤
        ENNReal.ofReal ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * M) + Step2.Q1 2 * mW) :=
    fun b hb => by rw [← Obs2.oTo_wA]; exact Sb_oA H hVl hWl hM.le hmW0 hVo hWo hb
  have hQ2 : 0 ≤ Step2.Q1 2 ^ 2 := sq_nonneg _
  have hSa0 : 0 ≤ (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * M) + Step2.Q1 2 * mW :=
    add_nonneg (mul_nonneg (mul_nonneg hL2 (mul_nonneg zero_le_two hQ2)) (mul_nonneg hτ.le hM.le))
      (mul_nonneg hQ0 hmW0)
  have hS1 : ∀ b ∈ blockIdx (L := L) (N := N) j, nw (ℓ' ^ 2) β (JT (SbO j C V W b)) ≤
      (2 * Step2.LastN.cSN 2 L + 4 * (L : ℝ) ^ 2 * Step2.Q1 2 ^ 2 + 2 * Step2.Q1 2) * τ :=
    fun b hb => by
      refine (nw_JT_le hℓ' hβ0 _ (mul_nonneg hcS hτ.le) hSa0 (hSe b hb)
        (hSa b hb)).trans ?_
      have e : 2 * β * ((L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * (τ * M) + Step2.Q1 2 * mW) =
          2 * (L : ℝ) ^ 2 * (2 * Step2.Q1 2 ^ 2) * τ * (β * M) + 2 * Step2.Q1 2 * (β * mW) := by ring
      have hβmW : β * mW ≤ τ := by
        calc β * mW ≤ β * (τ * M) := mul_le_mul_of_nonneg_left hmW hβ0
          _ = τ * (β * M) := by ring
          _ = τ := by rw [hβM, mul_one]
      rw [e, hβM, mul_one]
      nlinarith
  have hcS1 : 0 ≤ 2 * Step2.LastN.cSN 2 L + 4 * (L : ℝ) ^ 2 * Step2.Q1 2 ^ 2 + 2 * Step2.Q1 2 := by
    have := mul_nonneg hL2 hQ2
    linarith
  have hS : ∑ b ∈ blockIdx (L := L) (N := N) j, nw (ℓ' ^ 2) β (JT (SbO j C V W b)) ≤ ρ := by
    refine (sum_le_card_nsmul _ _ _ hS1).trans ?_
    rw [nsmul_eq_mul, hρ, cRho]
    have := mul_le_mul_of_nonneg_right hn (mul_nonneg hcS1 hτ.le)
    nlinarith [mul_nonneg hL2 (mul_nonneg hcS hτ.le), mul_nonneg hL2 (mul_nonneg hQ0 hτ.le),
      mul_nonneg hL2 (mul_nonneg hL2 (mul_nonneg hcS hτ.le))]
  have hy : ∑ b ∈ blockIdx (L := L) (N := N) j,
      ℓ' ^ 2 * ‖Suscept.c2 ((YpN C V b : SA .two (Lam 2 L N)).e)‖ ≤ ρ := by
    have h1 : ∀ b ∈ blockIdx (L := L) (N := N) j,
        ℓ' ^ 2 * ‖Suscept.c2 ((YpN C V b : SA .two (Lam 2 L N)).e)‖ ≤ 2 * (Step2.Q1 2 * τ) :=
      fun b hb => c2_le_of_Tj hℓ' (by have := mul_nonneg hQ0 hτ.le; linarith) (by
        show Tj 2 (L : ℝ) (j + 1) ℓ' ((bulk (YpN C V b) : EvR (Lam 2 L N)) : Alg 2 L N) ≤ _
        rw [bulk_YpN]; exact H.VpN_le hb)
    refine (sum_le_card_nsmul _ _ _ h1).trans ?_
    rw [nsmul_eq_mul, hρ, cRho]
    have := mul_le_mul_of_nonneg_right hn (show 0 ≤ 2 * (Step2.Q1 2 * τ) by
      have := mul_nonneg hQ0 hτ.le; linarith)
    nlinarith [mul_nonneg hL2 (mul_nonneg hcS hτ.le), mul_nonneg hL2 (mul_nonneg hQ0 hτ.le),
      mul_nonneg hL2 (mul_nonneg hL2 (mul_nonneg hcS hτ.le)),
      mul_nonneg hL2 (mul_nonneg hL2 (mul_nonneg (sq_nonneg (Step2.Q1 2)) hτ.le))]
  have hB : ∑ b ∈ blockIdx (L := L) (N := N) j,
      ℓ' ^ 2 * β * ‖Suscept.c2 ((VprO C V b : SA .two (Lam 2 L N)).a)‖ ≤ (L : ℝ) ^ 2 * Step2.Q1 2 := by
    have h1 : ∀ b ∈ blockIdx (L := L) (N := N) j,
        ℓ' ^ 2 * β * ‖Suscept.c2 ((VprO C V b : SA .two (Lam 2 L N)).a)‖ ≤ Step2.Q1 2 :=
      fun b hb => by
        have h := c2_le_of_Tj (L := L) (N := N) (k := j + 1) hℓ' (mul_nonneg hQ0 hM.le)
          (x := (VprO C V b : SA .two (Lam 2 L N)).a) (by
            rw [← Obs2.oTo_wA]; exact Vpr_oA H hVl hVo hb)
        calc ℓ' ^ 2 * β * ‖Suscept.c2 ((VprO C V b : SA .two (Lam 2 L N)).a)‖
            = β * (ℓ' ^ 2 * ‖Suscept.c2 ((VprO C V b : SA .two (Lam 2 L N)).a)‖) := by ring
          _ ≤ β * (Step2.Q1 2 * M) := mul_le_mul_of_nonneg_left h hβ0
          _ = Step2.Q1 2 * (β * M) := by ring
          _ = Step2.Q1 2 := by rw [hβM, mul_one]
    refine (sum_le_card_nsmul _ _ _ h1).trans ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hn hQ0
  have hk : nw (ℓ' ^ 2) β (JT (KNO j C V W K univ)) ≤ κ := by
    refine (nw_JT_le hℓ' hβ0 _ (by positivity) (by positivity) hKe hKa).trans ?_
    have e : 2 * β * (τ * M / r₀ ^ 2) = 2 * (τ / r₀ ^ 2) * (β * M) := by ring
    rw [e, hβM, mul_one, hκ]
    have h1 : τ / r₀ ≤ τ / r₀ ^ 2 := div_le_div_of_nonneg_left hτ.le (by positivity)
      (by nlinarith)
    have : 4 * τ / r₀ ^ 2 = 2 * (τ / r₀ ^ 2) + 2 * (τ / r₀ ^ 2) := by ring
    linarith
  have hx : ‖∑ b ∈ blockIdx (L := L) (N := N) j,
      ε ((LSO P j C V W b : SA .two (Lam 2 L N)).e)‖ ≤ ρ := by
    have hw : ∀ b ∈ blockIdx (d := 2) (L := L) (N := N) j,
        ‖ε (Step2.Sb j C (bulkF V) (bulkF W) b : Alg 2 L N)‖ ≤ Step2.LastN.cSN 2 L * τ :=
      fun b hb => eps_le_of_Tj hℓ' (mul_nonneg hcS hτ.le) (H.Sb_le hb)
    have h1 : ∀ b ∈ blockIdx (L := L) (N := N) j,
        ‖ε ((LSO P j C V W b : SA .two (Lam 2 L N)).e)‖ ≤ (L : ℝ) ^ 2 * (Step2.LastN.cSN 2 L * τ) :=
      fun b _ => by
        show ‖ε ((bulk (LSO P j C V W b) : EvR (Lam 2 L N)) : Alg 2 L N)‖ ≤ _
        rw [bulk_LSO]
        exact eps_LS_le j C (bulkF V) (bulkF W) hj (mul_nonneg hcS hτ.le) hw b
    refine (norm_sum_le _ _).trans ((sum_le_card_nsmul _ _ _ h1).trans ?_)
    rw [nsmul_eq_mul, hρ, cRho]
    have := mul_le_mul_of_nonneg_right hn (show 0 ≤ (L : ℝ) ^ 2 * (Step2.LastN.cSN 2 L * τ) by
      positivity)
    nlinarith [mul_nonneg hL2 (mul_nonneg hcS hτ.le), mul_nonneg hL2 (mul_nonneg hQ0 hτ.le),
      mul_nonneg hL2 (mul_nonneg hL2 (mul_nonneg (sq_nonneg (Step2.Q1 2)) hτ.le))]
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ ≤ 1 := by rw [hκ, div_le_one (by positivity)]; exact hsm2
  obtain ⟨c1, c2⟩ := finG_jet_le P j C V W K hj (by positivity) hβ0 hS hy hB hk hx hsm hκ0 hκ1
  have hfin : 60 * (1 + (L : ℝ) ^ 2 * Step2.Q1 2) * (ρ + κ) * M =
      cJet L * (cRho L + 4 / r₀ ^ 2) * τ * M := by
    rw [hρ, hκ, cJet]; ring
  constructor
  · have := mul_le_mul_of_nonneg_right c1 hM.le
    rw [← hfin]
    calc ℓ' ^ 2 * ‖_‖ = ℓ' ^ 2 * β * ‖_‖ * M := by
          rw [mul_assoc (ℓ' ^ 2) β, mul_comm β, mul_assoc, mul_assoc, hβM, mul_one]
      _ ≤ _ := this
  · have := mul_le_mul_of_nonneg_right c2 hM.le
    rw [← hfin]
    calc ‖ε ((finG P j C V W K : SA .two (Lam 2 L N)).a)‖ =
          β * ‖ε ((finG P j C V W K : SA .two (Lam 2 L N)).a)‖ * M := by
          rw [mul_comm β, mul_assoc, hβM, mul_one]
      _ ≤ _ := this

end

end PtCorr2
