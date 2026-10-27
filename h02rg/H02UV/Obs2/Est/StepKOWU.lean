import Obs2.Est.StepKOW
import Obs2.Est.Step3OLU

/-!
# Theorem `stepK` for unreduced inputs, two regulators (copy of `Obs2.Est.StepKOWAB`)

**`stepKO_tsWU`**: `stepKO_tsWAB` for inputs with one-point parts (no `abSub`, no anchoring),
`K(X)_{ab} = 0` on small sets, single-source supports, and the `V` sizes halved (`‖V‖ ≤ ḡ/2`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

set_option maxHeartbeats 2000000 in
/-- **Theorem `stepK` with sources**, input regulator `A`, output regulator `μA` (`μ ≥ 1`). -/
theorem stepKO_tsWU (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ μ : ℝ, 1 ≤ μ → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt), w.Sub → w.a ≠ ⊤ → w.b ≠ ⊤ → w.ab ≠ ⊤ →
    ∀ (V W : OFam c d L N) (K : OAct c d L N),
      (∀ X, IsConn j X → P.a ∉ nbhd j X → (K X : SA c (Lam d L N)).a = 0) →
      (∀ X, IsConn j X → P.b ∉ nbhd j X → (K X : SA c (Lam d L N)).b = 0) →
      (∀ X, IsSmall j X → (K X : SA c (Lam d L N)).ab = 0) →
      InF j (bulkF V) → InF j (bulkF W) →
      (∀ b, ε ((bulkF V b : EvR (Lam d L N)) : Alg d L N) = 0) → InK2 j (bulkF K) →
      OLocS P j V W K →
      (∀ X, IsConn j X → IsSymS (K X : SA c (Lam d L N))) →
      ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal (g / 2) → Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal (g ^ 2) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal (g / 2)) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (W b) ≤ ENNReal.ofReal (g ^ 2)) →
      ∀ k : ℝ, 0 ≤ k → k ≤ ε₀ →
      Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal k →
      (∀ X, IsConn j X →
        ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ ENNReal.ofReal k) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal ((μ * A) ^ (nb (j + 1) U - 2 ^ d)) *
          oTj d L w (j + 1) ℓ' (KplusO P j C V W K U : SA c (Lam d L N)) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) * k) +
          ENNReal.ofReal (C₁ * (g ^ 3 + g * k + k ^ 2)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound d hd1
  obtain ⟨Clo, hClo0, hlocO⟩ := exists_LocO2_full_bound d (by omega)
  obtain ⟨cN, hcN⟩ := card_small_containing d
  set lam : ℝ := 2 * (2 : ℝ) ^ (1 + cN) with hlamdef
  have hlam1 : 1 ≤ lam := by
    have : (1 : ℝ) ≤ 2 ^ (1 + cN) := one_le_pow₀ (by norm_num)
    rw [hlamdef]; linarith
  obtain ⟨C₀, η, L₃, hC₀, hη, h3⟩ := step3OLU d hd
  refine ⟨C₀, η, max L₃ (max (2 ^ (d + 3) + 8 * d + 1) ⌈pauliL0 d⌉₊), hC₀, hη, ?_⟩
  intro L _ hL μ hμw
  have hL3 : L₃ ≤ L := le_trans (le_max_left _ _) hL
  have hL8 : 2 ^ (d + 3) + 8 * d < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL)
  have hLp : pauliL0 d ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL)
  have hL2 : 2 ^ (d + 2) ≤ L := by
    have : 2 ^ (d + 2) ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨A₀, hA₀, h3'⟩ := h3 L hL3 (lam * μ) (one_le_mul_of_one_le_of_one_le hlam1 hμw)
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := hA₀.trans hA
  have hA0 : 0 < A := by linarith
  have hμA1 : 1 ≤ μ * A := one_le_mul_of_one_le_of_one_le hμw hA1
  have hμA0 : 0 < μ * A := by linarith
  obtain ⟨ε₃, C₃, hε₃, hC₃, h3''⟩ := h3' A hA
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
  set n₀ : ℝ := (L : ℝ) ^ d with hn₀
  have hn₀0 : 0 ≤ n₀ := by positivity
  set cB : ℕ := (2 ^ (d + 1) + 3) ^ d
  set a : ℝ := 2 * (2 : ℝ) ^ (1 + cN) * (μ * A) with ha
  have ha0 : 0 ≤ a := by positivity
  set X1 : ℝ := a ^ cB with hX1
  have hX10 : 0 ≤ X1 := by positivity
  set Cδ : ℝ := (2 : ℝ) ^ (2 ^ d) * (2 : ℝ) ^ (L ^ d * 2 ^ d) * ((cNear d L + 2) * (6 * Q1 d ^ 2))
    with hCδ
  have hCδ0 : 0 ≤ Cδ := by positivity
  set C0' : ℝ := C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) with hC0'
  have hC0'0 : 0 ≤ C0' := by positivity
  set Λ2 : ℝ := (lam * (μ * A)) ^ 2 ^ d with hΛ2
  have hΛ20 : 0 ≤ Λ2 := by positivity
  set Cμ : ℝ := C0' + 3 * C₃ with hCμ
  have hCμ0 : 0 ≤ Cμ := by positivity
  set Cx : ℝ := X1 ^ 2 * Cδ ^ 2 + X1 * Cδ * Λ2 * (C0' + C₃) with hCx
  have hCx0 : 0 ≤ Cx := by positivity
  set ε₀ : ℝ := min ε₃ (min 1 (min (1 / (2 * n₀ * cG + 1))
    (min (1 / (X1 * Cδ + 1)) (1 / (Cμ * Λ2 + 1))))) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hε₃ (lt_min one_pos (lt_min (by positivity)
    (lt_min (by positivity) (by positivity))))
  refine ⟨ε₀, C₃ + Cx, hε₀0, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw hwa hwb hwab V W K hza hzb hKs hV hW hV0 hK HL hsym
    g hg0 hgε hVg hWg hVo hWo k hk0 hkε hKk hKo U hU
  have e1 : ε₀ ≤ ε₃ := min_le_left _ _
  have e2 : ε₀ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have e5 : ε₀ ≤ 1 / (2 * n₀ * cG + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e6 : ε₀ ≤ 1 / (X1 * Cδ + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e7 : ε₀ ≤ 1 / (Cμ * Λ2 + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
  -- locality
  have hlocV : ∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
      (V b : SA c (Lam d L N)) := fun b => cmpInA_of_osub (HL.hV b)
  have hlocW : ∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
      (W b : SA c (Lam d L N)) := fun b => cmpInA_of_osub (HL.hW b)
  have hlocK : ∀ X, IsConn j X → CmpInA (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N)) :=
    fun X hX => cmpInA_of_osub (HL.hK X hX)
  -- the radius
  set r := max g k with hrdef
  have hr0 : 0 ≤ r := le_max_of_le_left hg0
  have hrε : r ≤ ε₀ := max_le hgε hkε
  have hr1 : r ≤ 1 := hrε.trans e2
  have hg1 : g ≤ 1 := hgε.trans e2
  have hk1 : k ≤ 1 := hkε.trans e2
  have hgr : g ≤ r := le_max_left _ _
  have hkr : k ≤ r := le_max_right _ _
  have hg2r : g ^ 2 ≤ r := (pow_le_of_le_one hg0 hg1 two_ne_zero).trans hgr
  have hVrh : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) j ℓ ((bulkF V b : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal (r / 2) :=
    fun b hb => ((le_iSup₂ (f := fun b (_ : b ∈ blockIdx (L := L) (N := N) j) =>
      Tj d (L : ℝ) j ℓ ((bulkF V b : EvR (Lam d L N)) : Alg d L N)) b hb).trans hVg).trans
        (ENNReal.ofReal_le_ofReal (by linarith))
  have hVr' : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj d (L : ℝ) j ℓ ((bulkF V b : EvR (Lam d L N)) : Alg d L N) ≤ ENNReal.ofReal r :=
    fun b hb => (hVrh b hb).trans (ENNReal.ofReal_le_ofReal (by linarith))
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
  have HO : BHOU P j ℓ ℓ' ℓC C V W K w r r r r Clo cS :=
    { hd := hd1, hLp := hLp, hL8 := hL8, hjN := hjN, hℓ := hℓ, hℓ' := hℓ', hℓC := hℓC,
      hsum := hsum, hC := hC, hw := hw, hVl := hlocV, hWl := hlocW
      hKl := fun X hX => hlocK X ⟨hX.1, hX.2.1⟩
      hr := hr0, hmV := hr0, hmW := hr0, hk := hr0, hVr := hVrh, hmVr := le_rfl
      hVm := fun b hb => (hVo b hb).trans (ENNReal.ofReal_le_ofReal (by linarith))
      hWm := fun b hb => (hWo b hb).trans (ENNReal.ofReal_le_ofReal hg2r)
      hKk := hKk', hCl := hClo0
      hloc := fun k' hk ℓ₀ hℓ₀ X Y hX hYX F hF =>
        hlocO L hL8 N c P w k' hk ℓ₀ hℓ₀ X Y hX hYX F hF
      hlocl := bho_hloclAB hd1 P j, hcS := hcS1, hcount := hcount }
  have H : BHFU P j ℓ ℓ' ℓC C V W K w A r Cl cS Clo :=
    ⟨HB, HO, hlocK, fun X hX => (hKo X hX).trans (ENNReal.ofReal_le_ofReal hkr)⟩
  -- `‖Ĩ_{j+1}(B_+)‖ ≤ 2`
  have hIt : ∀ c' : Fin d → ℕ, H.nS.nrm (ItO P j C V W K c') ≤ ENNReal.ofReal 2 := by
    intro c'
    refine (H.ItO_full c').trans (ENNReal.ofReal_le_ofReal ?_)
    have htG := H.tG_le
    have htG0 := H.htG
    have hx : (L : ℝ) ^ d * BHFU.tG d L r Cl Clo cS ≤ 1 / 2 := by
      have h1 : 2 * n₀ * cG * r ≤ 1 :=
        le_one_of_le_div (by positivity) (by positivity) (hrε.trans e5) (by linarith)
      have h2 : (L : ℝ) ^ d * BHFU.tG d L r Cl Clo cS ≤ n₀ * (cG * r) :=
        mul_le_mul_of_nonneg_left htG hn₀0
      have e : n₀ * (cG * r) = (2 * n₀ * cG * r) / 2 := by ring
      linarith only [h1, h2, e]
    have he : Real.exp (1 / 2) ≤ 2 := by
      have := (abs_le.1 (Real.abs_exp_sub_one_le (x := 1 / 2) (by norm_num))).2
      norm_num at this ⊢; linarith
    exact (Real.exp_le_exp.2 hx).trans he
  -- the second-order data
  set δ : ℝ := Cδ * r ^ 2 with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hJb : ∀ p ∈ pairsU (L := L) (N := N) (j + 1),
      H.nS.nrm (JbarO (j + 1) (ItO P j C V W K) (JhO j C V) p.1 p.2) ≤ ENNReal.ofReal δ := by
    intro p hp
    obtain ⟨-, hs, -⟩ := mem_pairsU.1 hp
    have hb1 : H.nS.nrm (bpowO (j + 1) (ItO P j C V W K) p.2) ≤
        ENNReal.ofReal (2 ^ (2 ^ d)) := by
      have := H.nS.prodR (blocks (j + 1) p.2) (ItO P j C V W K)
        (fun _ => 2) (fun _ _ => by norm_num) (fun c' _ => hIt c')
      rw [prod_const] at this
      exact this.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num) hs.2.2))
    have hnb : nb j p.2 ≤ L ^ d * 2 ^ d :=
      (nb_le_of_succ hs.1).trans (Nat.mul_le_mul_left _ hs.2.2)
    have hb2 := H.JhO_full p.1 hs.1
    have hb2' : H.nS.nrm (JhO j C V p.1 p.2) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (L ^ d * 2 ^ d) * ((cNear d L + 2) * (6 * Q1 d ^ 2 * r ^ 2))) := by
      refine hb2.trans (ENNReal.ofReal_le_ofReal ?_)
      have e : BHFU.qP d r = 6 * Q1 d ^ 2 * r ^ 2 := by unfold BHFU.qP; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hnb) (by positivity)
    refine (H.nS.mulR (by positivity) hb1 hb2').trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hδdef, hCδ]; ring
  -- the bound on `M = K^♯`
  set yy : ℝ := g ^ 3 + g * k + k ^ 2 with hyy
  have hyy0 : 0 ≤ yy := by positivity
  set μ' : ℝ := C0' * k + C₃ * yy with hμdef
  have hμ0 : 0 ≤ μ' := by positivity
  have hM : ∀ Y, IsConn (j + 1) Y → ENNReal.ofReal ((lam * (μ * A)) ^ (nb (j + 1) Y - 2 ^ d)) *
      H.nS.nrm (KnewO P j C V W K Y) ≤ ENNReal.ofReal μ' := by
    intro Y hY
    have := h3'' N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw hwa hwb hwab V W K hza hzb hKs hV hW hV0 hK
      hlocV hlocW hlocK hsym g hg0 (hgε.trans e1) hVg hWg hVo hWo k hk0 (hkε.trans e1)
      hKk hKo Y hY
    rw [show lam * (μ * A) = lam * μ * A by ring]
    refine this.trans (le_of_eq ?_)
    rw [hμdef, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  -- smallness
  have hδ1 : (2 * (2 : ℝ) ^ (1 + cN) * (μ * A)) ^ ((2 ^ (d + 1) + 3) ^ d) * δ ≤ 1 := by
    have h := le_one_of_le_div (x := X1 * Cδ) (by positivity) (by positivity) (hrε.trans e6)
      (by linarith)
    have hr2 : r ^ 2 ≤ r := by rw [pow_two]; exact mul_le_of_le_one_left hr0 hr1
    calc (2 * (2 : ℝ) ^ (1 + cN) * (μ * A)) ^ ((2 ^ (d + 1) + 3) ^ d) * δ = X1 * Cδ * r ^ 2 := by
          rw [hX1, ha, hδdef]; ring
      _ ≤ X1 * Cδ * r := by gcongr
      _ ≤ 1 := h
  have hμ1 : μ' * (lam * (μ * A)) ^ 2 ^ d ≤ 1 := by
    have h := le_one_of_le_div (x := Cμ * Λ2) (by positivity) (by positivity) (hrε.trans e7)
      (by linarith)
    have hμr : μ' ≤ Cμ * r := by
      have h2 : yy ≤ 3 * r := by
        have i1 : g ^ 3 ≤ r := (pow_le_of_le_one hg0 hg1 (by norm_num)).trans hgr
        have i2 : g * k ≤ r := (mul_le_of_le_one_left hk0 hg1).trans hkr
        have i3 : k ^ 2 ≤ r := (pow_le_of_le_one hk0 hk1 (by norm_num)).trans hkr
        rw [hyy]; linarith
      calc μ' = C0' * k + C₃ * yy := rfl
        _ ≤ C0' * r + C₃ * (3 * r) := by gcongr
        _ = Cμ * r := by rw [hCμ]; ring
    calc μ' * (lam * (μ * A)) ^ 2 ^ d = μ' * Λ2 := rfl
      _ ≤ Cμ * r * Λ2 := by gcongr
      _ = Cμ * Λ2 * r := by ring
      _ ≤ 1 := h
  -- the decomposition
  have hCR : CovRange j C := fun x y h => hC.range hjN x y h
  have hJ0 : ∀ b ∈ blockIdx (L := L) (N := N) (j + 1),
      ∑ U ∈ (smallSets (d := d) (L := L) (N := N) (j + 1)).filter
        (fun U => blockSet (j + 1) b ⊆ U), JhO j C V b U = 0 :=
    fun b _ => JhO_sum_U HL hd1 hL2 hjN hCR b
  have hsplit : KplusO P j C V W K U = KnewO P j C V W K U +
      ∑ g ∈ Rset (j + 1) U, RtermO (j + 1) (ItO P j C V W K) (KnewO P j C V W K) (JhO j C V) U g :=
    KoutO_split hJ0 hU
  have hE := KoutO_sub_le H.nS (k := j + 1) (I := ItO P j C V W K) (M := KnewO P j C V W K)
    (J := JhO j C V) hjN.le hμA1 hlam1 hδ0 hμ0
    (fun b hb => by convert hcN L N (j + 1) b hb) le_rfl (fun b _ => hIt b) hJb hM hδ1 hμ1 hU.1
  rw [← H.nS_nrm, hsplit]
  refine (mul_le_mul_left' (H.nS.add _ _) _).trans ?_
  rw [mul_add]
  have hmono : ENNReal.ofReal ((μ * A) ^ (nb (j + 1) U - 2 ^ d)) *
      H.nS.nrm (KnewO P j C V W K U) ≤
      ENNReal.ofReal ((lam * μ * A) ^ (nb (j + 1) U - 2 ^ d)) * H.nS.nrm (KnewO P j C V W K U) :=
    mul_le_mul_right' (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hμA0.le
      ((le_mul_of_one_le_left hμA0.le hlam1).trans_eq (by ring)) _)) _
  have hS3' := h3'' N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw hwa hwb hwab V W K hza hzb hKs hV hW hV0 hK
    hlocV hlocW hlocK hsym g hg0 (hgε.trans e1) hVg hWg hVo hWo k hk0 (hkε.trans e1)
    hKk hKo U hU
  refine (add_le_add (hmono.trans hS3') hE).trans ?_
  -- the real inequality for the correction
  have hX1' : (2 * (2 : ℝ) ^ (1 + cN) * (μ * A)) ^ ((2 ^ (d + 1) + 3) ^ d) = X1 := by rw [hX1, ha]
  rw [← hyy, hX1']
  have hcorr : X1 * δ * (X1 * δ + μ' * (lam * (μ * A)) ^ 2 ^ d) ≤ Cx * yy :=
    corr_real hg0 hk0 hg1 hk1 hX10 hCδ0 hΛ20 hC0'0 hC₃
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e4 : (C₃ + Cx) * yy = C₃ * yy + Cx * yy := by ring
  rw [e4]; linarith

end

end Obs2
