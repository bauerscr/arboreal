import Obs2.Est.Step3OL
import Obs2.Est.Step3OAB

/-!
# The reapportioned activity on the `σ_aσ_b` sector (`ab` copy of `Obs2.Est.Step3OL`)

**`step3OLAB`**: `Obs2.step3OL` under the hypotheses of `step2O_tsLAB` (inputs in `abSub`,
`K(X)` anchored, all components local, finite weights with `w.Sub`): for every connected
`(j+1)`-polymer `U`,
`(λA)^{(|𝓑_{j+1}(U)| - 2^d)_+} ‖K^♯_{j+1}(U)‖ ≤ C₀ (L^{d-3} + A^{-η}) k + C₁(ḡ³ + ḡk + k²)`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

set_option maxHeartbeats 1000000 in
/-- **Theorem `step3` with sources**, output regulator `λA`. -/
theorem step3OLAB (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ lam : ℝ, 1 ≤ lam → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt), w.Sub → w.a ≠ ⊤ → w.b ≠ ⊤ → w.ab ≠ ⊤ →
    ∀ (V W : OFam c d L N) (K : OAct c d L N),
      (∀ b, V b ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ b, W b ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ X, IsConn j X → K X ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ X, IsConn j X → K X ∈ (anc P X : Subalgebra ℂ (OE c (Lam d L N)))) →
      InF j (bulkF V) → InF j (bulkF W) →
      (∀ b, ε ((bulkF V b : EvR (Lam d L N)) : Alg d L N) = 0) → InK2 j (bulkF K) →
      (∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
        (V b : SA c (Lam d L N))) →
      (∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
        (W b : SA c (Lam d L N))) →
      (∀ X, IsConn j X → CmpInA (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N))) →
      (∀ X, IsConn j X → IsSymS (K X : SA c (Lam d L N))) →
      ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal g → Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal (g ^ 2) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal g) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (W b) ≤ ENNReal.ofReal (g ^ 2)) →
      ∀ k : ℝ, 0 ≤ k → k ≤ ε₀ →
      Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal k →
      (∀ X, IsConn j X →
        ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ ENNReal.ofReal k) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) *
          oTj d L w (j + 1) ℓ' (KnewO P j C V W K U : SA c (Lam d L N)) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) * k) +
          ENNReal.ofReal (C₁ * (g ^ 3 + g * k + k ^ 2)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, η, L₂, hC₀, hη, h2⟩ := step2O_tsLAB d hd
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd1
  obtain ⟨Clo, hClo0, hlocO⟩ := exists_LocO2_ab_bound d (by omega)
  obtain ⟨cN, hcN⟩ := card_small_containing d
  refine ⟨C₀, η, max L₂ (max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊), hC₀, hη, ?_⟩
  intro L _ hL lam hlam
  have hL2 : L₂ ≤ L := le_trans (le_max_left _ _) hL
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨A₀, hA₀, h2'⟩ := h2 L hL2 lam hlam
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := hA₀.trans hA
  have hA0 : 0 < A := by linarith
  obtain ⟨ε₂, C₂, hε₂, hC₂, h2''⟩ := h2' A hA
  set cS : ℝ := cN + 1 with hcSdef
  have hcS1 : 1 ≤ cS := by rw [hcSdef]; linarith [Nat.cast_nonneg (α := ℝ) cN]
  have hQ := one_le_Q1 hd1
  have hn : 0 ≤ cNear d L := Nat.cast_nonneg _
  have hcu : 0 ≤ cUblk d L Cl cS := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    simp only [cUblk, cSblk, cNear]; positivity
  have hcw : 0 ≤ cWblk d L Cl := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (d + 3) + 7) ^ d)
    simp only [cWblk, cSblk, cNear]; positivity
  have hcSo0 : 0 ≤ cSo d L := by
    have := mul_nonneg (mul_nonneg zero_le_two hn) (sq_nonneg (Q1 d))
    unfold cSo; linarith
  have hcuo : 0 ≤ cUo d L Clo cS := by
    have h1 : 0 ≤ Q1 d * pq d ^ 2 * (cS * Clo) := by
      have := one_le_pq hd1; positivity
    have h2 : 0 ≤ Clo * ((L : ℝ) ^ d * cSo d L) := by positivity
    unfold cUo; linarith
  have hcwo : 0 ≤ cWo d L Clo := by
    have h2 : 0 ≤ Clo * ((L : ℝ) ^ d * cSo d L) := by positivity
    unfold cWo; linarith
  set cG : ℝ := 2 * cUblk d L Cl cS + 2 * cUo d L Clo cS + cWblk d L Cl + cWo d L Clo with hcG
  have hcG0 : 0 ≤ cG := by positivity
  set n₀ : ℝ := 2 * (L : ℝ) ^ d with hn₀
  have hn₀0 : 0 ≤ n₀ := by positivity
  set Ck : ℝ := (2 : ℝ) ^ (2 * L ^ d) * ((cNear d L + 2) * (6 * Q1 d ^ 2)) with hCk
  have hCk0 : 0 ≤ Ck := by positivity
  set Cs : ℝ := 2 * n₀ * cG * Ck with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  set ε₀ : ℝ := min ε₂ (min 1 (1 / (n₀ * cG + 1))) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε₂ (lt_min one_pos (by positivity))
  refine ⟨ε₀, C₂ + Cs, hε₀0, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw hwa hwb hwab V W K hVab hWab hKab hKanc hV hW hV0 hK hlocV hlocW
    hlocK hsym g hg0 hgε hVg hWg hVo hWo k hk0 hkε hKk hKo U hU
  have e1 : ε₀ ≤ ε₂ := min_le_left _ _
  have e2 : ε₀ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have e3 : ε₀ ≤ 1 / (n₀ * cG + 1) := (min_le_right _ _).trans (min_le_right _ _)
  -- the step2 bound
  have hS2 := h2'' N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw hwa hwb hwab V W K hVab hWab hKab hKanc hV hW hV0 hK
    hlocV hlocW hlocK hsym g hg0 (hgε.trans e1) hVg hWg hVo hWo k hk0 (hkε.trans e1)
    hKk hKo U hU
  -- the radius
  set r := max g k with hrdef
  have hr0 : 0 ≤ r := le_max_of_le_left hg0
  have hrε : r ≤ ε₀ := max_le hgε hkε
  have hr1 : r ≤ 1 := hrε.trans e2
  have hg1 : g ≤ 1 := hgε.trans e2
  have hk1 : k ≤ 1 := hkε.trans e2
  have hgr : g ≤ r := le_max_left _ _
  have hkr : k ≤ r := le_max_right _ _
  have hg2r : g ^ 2 ≤ r := by nlinarith
  have hj : j < N := by omega
  have hVr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) j ℓ ((bulkF V b : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal r :=
    fun b hb => ((le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj d (L : ℝ) j ℓ ((bulkF V b : EvR (Lam d L N)) : Alg d L N)) b hb).trans hVg).trans
        (ENNReal.ofReal_le_ofReal hgr)
  have hWr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) j ℓ ((bulkF W b : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal r :=
    fun b hb => ((le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj d (L : ℝ) j ℓ ((bulkF W b : EvR (Lam d L N)) : Alg d L N)) b hb).trans hWg).trans
        (ENNReal.ofReal_le_ofReal hg2r)
  have hcount : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
      (((smallSets (d := d) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card : ℝ) ≤ cS := fun b hb => by
    have h1 : ((smallSets (d := d) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card ≤ cN := by convert hcN L N j b hb
    have h2 := Nat.cast_le (α := ℝ) |>.2 h1
    linarith
  have HB : Step2.BH j ℓ ℓ' ℓC C (bulkF V) (bulkF W) (bulkF K) A r Cl cS :=
    { hd := hd1, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hV := hV, hW := hW, hV0 := hV0, hK := hK, hA := hA1, hr := hr0,
      hr1 := hr1, hVr := hVr', hWr := hWr', hKr := hKk.trans (ENNReal.ofReal_le_ofReal hkr),
      hCl := hCl0
      hloc := fun k hk ℓ₀ hℓ₀ X Y hX hYX F hF => hloc L hL8 N k hk X Y hX hYX F hF ℓ₀ hℓ₀
      hcS := hcS1, hcount := hcount }
  have hKk' : ∀ X, IsSmall j X → oTo w j ℓ (K X) ≤ ENNReal.ofReal r := fun X hX => by
    have h := hKo X ⟨hX.1, hX.2.1⟩
    rw [show nb j X - 2 ^ d = 0 from Nat.sub_eq_zero_of_le hX.2.2, pow_zero,
      ENNReal.ofReal_one, one_mul] at h
    exact h.trans (ENNReal.ofReal_le_ofReal hkr)
  have HO : BHOAB P j ℓ ℓ' ℓC C V W K w r r r r Clo cS :=
    { hd := hd1, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hw := hw, hVab := hVab, hWab := hWab
      hKab := fun X hX => hKab X ⟨hX.1, hX.2.1⟩, hVl := hlocV, hWl := hlocW
      hKl := fun X hX => hlocK X ⟨hX.1, hX.2.1⟩
      hr := hr0, hmV := hr0, hmW := hr0, hk := hr0, hVr := hVr'
      hVm := fun b hb => (hVo b hb).trans (ENNReal.ofReal_le_ofReal hgr)
      hWm := fun b hb => (hWo b hb).trans (ENNReal.ofReal_le_ofReal hg2r)
      hKk := hKk', hCl := hClo0
      hloc := fun k' hk ℓ₀ hℓ₀ X Y hX hYX F hFab hF =>
        hlocO L hL8 N c P w k' hk ℓ₀ hℓ₀ X Y hX hYX F hFab hF.ab
      hlocl := bho_hloclAB hd1 P j, hcS := hcS1, hcount := hcount }
  have H : BHFAB P j ℓ ℓ' ℓC C V W K w A r Cl cS Clo :=
    ⟨HB, HO, hlocK, fun X hX => (hKo X hX).trans (ENNReal.ofReal_le_ofReal hkr)⟩
  -- the reapportionment term
  have hsplit : KnewO P j C V W K U = (Knext2O P j C V W K U - K2O j C V U) +
      -((bpowO j (GpO P j C V W K) U - 1) * K2O j C V U) := by rw [KnewO]; ring
  have hT : ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) *
      H.nS.nrm ((bpowO j (GpO P j C V W K) U - 1) * K2O j C V U) ≤
      ENNReal.ofReal (Cs * r ^ 3) := by
    by_cases hU2 : 2 < nb (j + 1) U
    · rw [K2O_eq_zero j C V hU2, mul_zero, H.nS.zero, mul_zero]; exact zero_le
    · push Not at hU2
      have hw1 : (lam * A) ^ (nb (j + 1) U - 2 ^ d) = 1 := by
        have : nb (j + 1) U - 2 ^ d = 0 := by
          have : 2 ≤ 2 ^ d := by
            calc 2 = 2 ^ 1 := rfl
              _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
          omega
        rw [this, pow_zero]
      rw [hw1, ENNReal.ofReal_one, one_mul]
      have hnbU' : nb j U ≤ 2 * L ^ d :=
        calc nb j U ≤ L ^ d * nb (j + 1) U := nb_le_of_succ hU.1
          _ ≤ L ^ d * 2 := Nat.mul_le_mul_left _ hU2
          _ = 2 * L ^ d := mul_comm _ _
      have hnbU : (nb j U : ℝ) ≤ n₀ := by
        rw [hn₀]; exact_mod_cast hnbU'
      have htG := H.tG_le
      have htG0 := H.htG
      have hx : (nb j U : ℝ) * BHFAB.tG d L r Cl Clo cS ≤ n₀ * cG * r := by
        calc (nb j U : ℝ) * BHFAB.tG d L r Cl Clo cS ≤ n₀ * (cG * r) :=
              mul_le_mul hnbU htG htG0 hn₀0
          _ = n₀ * cG * r := by ring
      have hnr : n₀ * cG * r ≤ 1 :=
        le_one_of_le_div (by positivity) (by positivity) (hrε.trans e3) (by linarith)
      have hP : H.nS.nrm (bpowO j (GpO P j C V W K) U - 1) ≤ ENNReal.ofReal (2 * (n₀ * cG * r)) := by
        refine (H.bpowO_GpO_sub_one U).trans (ENNReal.ofReal_le_ofReal ?_)
        have := exp_sub_one_le (mul_nonneg (Nat.cast_nonneg _) htG0) (hx.trans hnr)
        linarith
      have hK2 : H.nS.nrm (K2O j C V U) ≤ ENNReal.ofReal (Ck * r ^ 2) := by
        refine (H.K2O_full hU.1).trans (ENNReal.ofReal_le_ofReal ?_)
        have h2n : (2 : ℝ) ^ nb j U ≤ 2 ^ (2 * L ^ d) := pow_le_pow_right₀ (by norm_num) hnbU'
        have e : BHFAB.qP d r = 6 * Q1 d ^ 2 * r ^ 2 := by unfold BHFAB.qP; ring
        rw [e, hCk]
        have h0 : 0 ≤ (cNear d L + 2) * (6 * Q1 d ^ 2 * r ^ 2) := by positivity
        calc (2 : ℝ) ^ nb j U * ((cNear d L + 2) * (6 * Q1 d ^ 2 * r ^ 2))
            ≤ (2 : ℝ) ^ (2 * L ^ d) * ((cNear d L + 2) * (6 * Q1 d ^ 2 * r ^ 2)) :=
              mul_le_mul_of_nonneg_right h2n h0
          _ = _ := by ring
      refine (H.nS.mulR (by positivity) hP hK2).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [hCs]; ring
  have hD : ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) *
      H.nS.nrm (Knext2O P j C V W K U - K2O j C V U) ≤
      ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) * k) +
      ENNReal.ofReal (C₂ * (g ^ 3 + g * k + k ^ 2)) := hS2
  rw [← H.nS_nrm, hsplit]
  refine (mul_le_mul_left' (H.nS.add _ _) _).trans ?_
  rw [H.nS.neg, mul_add]
  refine (add_le_add hD hT).trans ?_
  -- `r³ ≤ g³ + k²`
  have hr3 : r ^ 3 ≤ g ^ 3 + g * k + k ^ 2 := by
    have hgk : 0 ≤ g * k := mul_nonneg hg0 hk0
    rcases le_total g k with h | h
    · have : r = k := max_eq_right h
      rw [this]
      have : k ^ 3 ≤ k ^ 2 := pow_le_pow_of_le_one hk0 hk1 (by norm_num)
      nlinarith [pow_nonneg hg0 3]
    · have : r = g := max_eq_left h
      rw [this]; nlinarith [sq_nonneg k]
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : Cs * r ^ 3 ≤ Cs * (g ^ 3 + g * k + k ^ 2) := mul_le_mul_of_nonneg_left hr3 hCs0
  have e : (C₂ + Cs) * (g ^ 3 + g * k + k ^ 2) =
      C₂ * (g ^ 3 + g * k + k ^ 2) + Cs * (g ^ 3 + g * k + k ^ 2) := by ring
  rw [e]; linarith

end

end Obs2
