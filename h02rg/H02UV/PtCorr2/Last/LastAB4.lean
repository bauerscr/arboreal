import PtCorr2.Pair.PairVStep4
import PtCorr2.Obs.ObsHistTop
import PtCorr2.Obs.ObsHistLast
import PtCorr2.Pair.PairDef5S
import PtCorr2.Pair.SeedSplit2

/-!
# The `ab` chain at the top step `N_h → N_h + 1` (`ValidAtL`)

Copies of the trajectory-level step lemmas of the `ab` chain at `j = N_h`, where only
`ValidAtL R N_h` holds (the raw facts are those of `hist_rawL`, with the same fields):

* **`hist_vstep_factsT`**: `hist_vstep_facts` at `j = N_h`;
* **`gradV_hist_leT`**: `gradV_hist_le` for `n ≤ N_h + 1` (the facts at `i = N_h` from
  `hist_vstep_factsT`);
* **`wobs_hist_stepABT`**, **`kobs_hist_stepABLT`**: `wobs_hist_stepAB`, `kobs_hist_stepABL` at
  `j = N_h`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 PolyAux

variable {L N : ℕ} [NeZero L]

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 1000000 in
/-- **`hist_vstep_facts` at the top scale `j = N_h`** (`ValidAtL`). -/
theorem hist_vstep_factsT (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) {j₀ : ℕ} (o₀ : ObsSt .two L N) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hjj : j₀ ≤ j) (hj : j = Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t) :
    GoodCov2 j (histS R (j + 1) t / 4) (histCovO R t j) ∧
    0 < histS R j t ∧ 0 < histS R (j + 1) t ∧
    ObsSymInv j (obsHistFrom R P j₀ o₀ j t) ∧
    OAnchS P j (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) (hKR R P j₀ o₀ t j) ∧
    (∀ X, IsSmall j X →
      (hKR R P j₀ o₀ t j X : SA .two (Lam 2 L N)).ab ∈ NX (nbhd j X : Set (Lam 2 L N))) ∧
    (∀ b ∈ blockIdx (L := L) (N := N) j,
      (SXO j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j)
        (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam 2 L N)).ab ∈
        NX (nbhd (j + 1) (Step2.Bp (L := L) (N := N) j b) : Set (Lam 2 L N))) ∧
    (∀ (w : Wt), w.Sub → ∀ k : ℝ,
      (∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).K X) ≤ ENNReal.ofReal k) →
      ∀ X, IsSmall j X → oTo w j (histS R j t) (hKR R P j₀ o₀ t j X) ≤ ENNReal.ofReal (8 * k)) := by
  subst hj
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, -, -, -, -, -, -, -, hsℓ, hsℓ'⟩ :=
    hist_rawL R hSB hV hm hβ hδ1 H hVL t ht
  have hval : ∀ i < j + 1, ValidCore R i ∧ RawInv R i (rawHist R i t) := fun i hi =>
    hist_validL R hV hVL t i (by omega)
  have hloc := obsLocInv_histFrom' R P hl0 t hjj fun i _ hi => hval i (by omega)
  have hsym := obsSymInv_histFrom' R P hs0 t hjj fun i _ hi => hval i (by omega)
  have hanc := obsAnchInv_histFrom' R P ha0 t hjj
  set st := rawHist R j t
  obtain ⟨hC0, -, -, -⟩ := HI.covL hVc
  have hC : GoodCov2 j (histS R (j + 1) t / 4) (histCovO R t j) := hC0
  have hjN : j + 1 < N := by
    have := hVc.1; omega
  have HL := olocS_full R P (t j).1 (t j).2.1 hVc HI (rawD_mem R st.u (t j).2.2) (rawK_mem R st.u (t j).2.2) hloc
  have HA : OAnchS P j (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) (hKR R P j₀ o₀ t j) :=
    oanchS_full R P _ _ hanc
  obtain ⟨-, hΔ⟩ := rg_inputs R j hVc st HI (t j).1 (t j).2.1 hmN hg _ hz hy hη
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hη0 : 0 ≤ cZ R * (t j).1 := (norm_nonneg _).trans hz
  refine ⟨hC, hsℓ, hsℓ', hsym, HA, fun X hX => (HL.hK X ⟨hX.1, hX.2.1⟩).2.2.2.1,
    fun b _ => (HL.SX_mem (by norm_num) (by have := hVc.2.2.1; omega) hjN
      (hC.range hjN) b).2.2.2.1, ?_⟩
  intro w hw k hk X hX
  have hA0 : 0 < R.A := Fact.out
  have h1 := oTo_fullK_leAB R j st (rawK R st.u (t j).2.2) (obsHistFrom R P j₀ o₀ j t) w hw hsℓ hA0
    (by positivity : (0 : ℝ) ≤ 8 * cM * R.ℓ ^ 2 * (cZ R * (t j).1)) (by linarith) hΔ X
  have hnb : nb j X - 2 ^ 2 = 0 := by
    have := hX.2.2; unfold nb; omega
  rw [hnb, pow_zero, pow_zero, ENNReal.ofReal_one] at h1
  simp only [one_mul] at h1
  have h2 := hk X ⟨hX.1, hX.2.1⟩
  rw [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h2
  calc oTo w j (histS R j t) (hKR R P j₀ o₀ t j X) ≤ ENNReal.ofReal 8 *
        oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).K X) := h1
    _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal k := mul_le_mul_right h2 _
    _ = ENNReal.ofReal (8 * k) := by rw [ENNReal.ofReal_mul (by norm_num)]

set_option maxHeartbeats 4000000 in
/-- **`gradV_hist_le` up to `n = N_h + 1`** (the top step `N_h` with `ValidAtL`). -/
theorem gradV_hist_leT (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (hNh : Nh + 2 ≤ N) (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (hL : 2 ^ (2 + 3) + 8 * 2 < L)
    {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin 2 → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir 2 → ℕ,
      Grassmann.mabs α ≤ pPhi 2 → ∀ u : Zd 2,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    {cSn cNn : ℝ}
    (hcS : ∀ i, ∀ b ∈ blockIdx (L := L) (N := N) i,
      (open Classical in ((smallSets (d := 2) (L := L) (N := N) i).filter
        (fun X => blockSet i b ⊆ X)).card : ℝ) ≤ cSn)
    (hcN : ∀ i (x : Lam 2 L N) (s : Finset (Fin 2 → ℕ)), s ⊆ blockIdx (L := L) (N := N) i →
      ((s.filter (fun b => x ∈ nbhd i (blockSet (L := L) (N := N) i b))).card : ℝ) ≤ cNn)
    (P : ObsPts 2 L N) (hab : P.a ≠ P.b) (w : List (Dir 2)) (hw : pathEnd P.a w = P.b)
    (hwl : (w.length : ℝ) ≤ 2 * ((supNorm (P.a - P.b) : ℕ) : ℝ))
    {j₀ : ℕ} (o₀ : ObsSt .two L N) (hl0 : ObsLocInv P j₀ o₀) (hs0 : ObsSymInv j₀ o₀)
    (ha0 : ObsAnchInv P j₀ o₀) (hvab : ObsVabInv P o₀)
    (hz : ∀ b, (o₀.V b : SA .two (Lam 2 L N)).ab = 0)
    (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (t : Flow2.Hist.Seq (Xs R)) {n : ℕ} (hjn : j₀ ≤ n) (hn : n ≤ Nh + 1)
    (ht : ∀ i ≤ Nh, Flow2.Hist.InDh Λ β δ κ cg cm cT ε i t)
    (hsL : 2 * ((supNorm (P.a - P.b) : ℕ) : ℝ) ≤ (L : ℝ) ^ (j₀ + 1))
    (wt : ℕ → ℝ) (hwt : ∀ i, 0 < wt i) (hw2 : ∀ i, j₀ ≤ i → i < n → wt i ≤ 2 * wt (i + 1))
    {Q₀ S₀ : ℝ} (hQ₀ : 0 ≤ Q₀) (hS₀ : 0 ≤ S₀)
    (hK : ∀ i, j₀ ≤ i → i < n → ∀ X, IsSmall i X →
      Tj 2 (L : ℝ) i (histS R i t) (hKR R P j₀ o₀ t i X : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (wt i * Q₀))
    (hS : ∀ i, j₀ ≤ i → i < n → ∀ b ∈ blockIdx (L := L) (N := N) i,
      Tj 2 (L : ℝ) (i + 1) (histS R (i + 1) t)
        (SXO i (histCovO R t i) (hVR R P j₀ o₀ t i) (hWR R P j₀ o₀ t i)
          (Step2.Bp (L := L) (N := N) i b) : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal (wt i * S₀)) :
    ∀ c ∈ blockIdx (L := L) (N := N) n,
      gradM4Sz {P.a} P.a P.b ((L : ℝ) ^ n) (histS R n t)
          (hVR R P j₀ o₀ t n c : SA .two (Lam 2 L N)).ab ≤
        wt n * (4 * ((2 * KG 2 Cc 4 + 3 * (9 / 8 : ℝ) ^ 2 + 2 * KM4 2 Cc) * (2 * cNn * cSn * Q₀) +
          (2 * KG 2 Cc 4 + 3 + 2 * KM4 2 Cc) * (2 * (L : ℝ) ^ 2 * S₀))) := by
  classical
  intro c hc
  have hne : (blockSet (L := L) (N := N) n c).Nonempty := by
    obtain ⟨x, -, hx⟩ := mem_image.1 hc
    exact ⟨x, mem_blockSet.2 hx⟩
  set B := blockSet (L := L) (N := N) n c with hB
  set s : ℝ := ((supNorm (P.a - P.b) : ℕ) : ℝ) with hsd
  have hs1 : 1 ≤ s := by
    have : supNorm (P.a - P.b) ≠ 0 := fun h => hab (sub_eq_zero.1 ((supNorm_eq_zero_iff _).1 h))
    rw [hsd]; exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  set ℓ : ℕ → ℝ := fun i => histS R i t with hℓd
  have hℓ : ∀ i, 0 < ℓ i := fun i => histS_pos' R hρ0 hρ t i
  have hℓq : ∀ i, ℓ (i + 1) ≤ 9 / 8 * ℓ i := fun i => histS_succ_le_q R hρ0 hρ t i
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hcS0 : 0 ≤ cSn := (Nat.cast_nonneg _).trans (hcS n c hc)
  have hcN0 : 0 ≤ cNn := by
    have := hcN n P.a ∅ (empty_subset _); simpa using this
  -- the facts of each step below `n`
  have hF := fun i (hi : j₀ ≤ i) (hin : i < n) =>
    if h : i < Nh then
      hist_vstep_facts R hSB hV hm hβ hδ1 H P o₀ hl0 hs0 ha0 t i hi h (ht i (by omega))
    else
      hist_vstep_factsT R hSB hV hm hβ hδ1 H P o₀ hl0 hs0 ha0 hVL hmN t i hi (by omega)
        (ht i (by omega))
  set κQ : ℕ → ℝ := fun i => ∑ b ∈ blocks i B,
    ∑ X ∈ (smallSets i).filter (fun X => blockSet i b ⊆ X),
      (Tj 2 (L : ℝ) i (ℓ i) (hKR R P j₀ o₀ t i X : SA .two (Lam 2 L N)).ab).toReal with hκQd
  set κS : ℕ → ℝ := fun i => ∑ b ∈ blocks i B,
    (Tj 2 (L : ℝ) (i + 1) (ℓ (i + 1))
      (SXO i (histCovO R t i) (hVR R P j₀ o₀ t i) (hWR R P j₀ o₀ t i)
        (Step2.Bp (L := L) (N := N) i b) : SA .two (Lam 2 L N)).ab).toReal with hκSd
  have hκQ : ∀ i, j₀ ≤ i → i < n → 0 ≤ κQ i ∧ κQ i ≤ wt i * (2 * cNn * cSn * Q₀) := by
    intro i hi hin
    refine ⟨sum_nonneg fun _ _ => sum_nonneg fun _ _ => ENNReal.toReal_nonneg, ?_⟩
    have := kappaQ_le_count P (hKR R P j₀ o₀ t i) B (hF i hi hin).2.2.2.2.1.hK
      (mul_nonneg (hwt i).le hQ₀) (hK i hi hin) (hcS i) (hcN i)
    calc κQ i ≤ 2 * cNn * cSn * (wt i * Q₀) := this
      _ = wt i * (2 * cNn * cSn * Q₀) := by ring
  have hκS : ∀ i, j₀ ≤ i → i < n → 0 ≤ κS i ∧ κS i ≤ wt i * (2 * (L : ℝ) ^ 2 * S₀) := by
    intro i hi hin
    refine ⟨sum_nonneg fun _ _ => ENNReal.toReal_nonneg, ?_⟩
    have HA := (hF i hi hin).2.2.2.2.1
    have := kappaS_le_count P (i := i)
      (fun U => (SXO i (histCovO R t i) (hVR R P j₀ o₀ t i) (hWR R P j₀ o₀ t i) U :
        SA .two (Lam 2 L N)).ab) B
      (fun b _ hn' => (SXO_Bp_anch (C := histCovO R t i) HA b).2.2 hn')
      (mul_nonneg (hwt i).le hS₀) (hS i hi hin)
    calc κS i ≤ 2 * (L : ℝ) ^ 2 * (wt i * S₀) := this
      _ = wt i * (2 * (L : ℝ) ^ 2 * S₀) := by ring
  -- the `μ_i`
  have hμ : ∀ i, j₀ ≤ i → i < n →
      ‖m4X P i (hVR R P j₀ o₀ t i) B‖ +
        ‖∑ b ∈ blocks i B, cfAB4 P.a P.b (Q2O P i (hKR R P j₀ o₀ t i) b : SA .two (Lam 2 L N)).ab‖ ≤
      ∑ i' ∈ Ico j₀ (i + 1), KM4 2 Cc * ((ℓ i')⁻¹ ^ 4 * (((L : ℝ) ^ i') ^ 2 / s ^ 2) * κQ i' +
        (ℓ (i' + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (i' + 1)) ^ 2 / s ^ 2) * κS i') := by
    intro i hi hin
    refine (m4X_hVR_mu_le R P j₀ o₀ t hvab hz (fun i' hi' hi'i => (hF i' hi' (by omega)).2.2.2.1)
      (fun i' _ hi'i => isPolymer_of_le (isPolymer_blockSet n c) (i' + 1) (by omega)) hi).trans
      (sum_le_sum fun i' hi' => ?_)
    obtain ⟨hji', hi'i⟩ := mem_Ico.1 hi'
    have hF' := hF i' hji' (by omega)
    exact m4SrcX_le_sizes R P j₀ o₀ t hCc0 hCc hL hab (by omega) B (hℓ i') (hℓ (i' + 1))
      hF'.2.2.2.2.2.1 hF'.2.2.2.2.2.2.1 le_rfl le_rfl
  -- covariance sizes
  have hCD : ∀ i, j₀ ≤ i → i < n →
      ‖histCovO R t i P.a P.a‖ ≤ (ℓ (i + 1) / 4) ^ 2 ∧
      ‖histCovO R t i P.a P.a - histCovO R t i P.b P.a‖ ≤
        2 * s * (ℓ (i + 1) / 4) ^ 2 / (L : ℝ) ^ (i + 1) ∧
      ‖histCovO R t i P.a P.a - histCovO R t i P.a P.b‖ ≤
        2 * s * (ℓ (i + 1) / 4) ^ 2 / (L : ℝ) ^ (i + 1) := by
    intro i hi hin
    obtain ⟨h1, h2, h3⟩ := covDiff_le_path (hF i hi hin).1 P.a w
    rw [hw] at h2 h3
    have hLp : (0 : ℝ) < (L : ℝ) ^ (i + 1) := pow_pos (by linarith) _
    have hx : (w.length : ℝ) * ((histS R (i + 1) t / 4) ^ 2 / (L : ℝ) ^ (i + 1)) ≤
        2 * s * (ℓ (i + 1) / 4) ^ 2 / (L : ℝ) ^ (i + 1) := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hwl (sq_nonneg _)) hLp.le
    exact ⟨h1, h2.trans hx, h3.trans hx⟩
  have H1 := gradM4Sz_hVR_block_sizesD R P j₀ o₀ t hCc0 hCc hL hab hvab hz (k := n) (by omega)
    (fun i hi hin => (hF i hi hin).2.2.2.1) hjn hne (q := 9 / 8) (by norm_num) ℓ hℓ
    (fun i _ _ => hℓq i) (fun i _ _ => (hℓq i).trans (by linarith [hℓ i]))
    (fun i => (ℓ (i + 1) / 4) ^ 2) (fun i => 2 * s * (ℓ (i + 1) / 4) ^ 2 / (L : ℝ) ^ (i + 1))
    (fun i => 2 * s * ((L : ℝ) ^ (i + 1))⁻¹)
    (fun i => ∑ i' ∈ Ico j₀ (i + 1), KM4 2 Cc * ((ℓ i')⁻¹ ^ 4 * (((L : ℝ) ^ i') ^ 2 / s ^ 2) *
      κQ i' + (ℓ (i' + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (i' + 1)) ^ 2 / s ^ 2) * κS i')) κQ κS
    (fun i hi hin => (hCD i hi hin).1) (fun i hi hin => (hCD i hi hin).2)
    (fun i _ _ => le_rfl) hμ
    (fun i hi hin => (hF i hi hin).2.2.2.2.2.1) (fun i hi hin => (hF i hi hin).2.2.2.2.2.2.1)
    (fun i _ _ => le_rfl) (fun i _ _ => le_rfl)
  have H2 := gamma_budget (Lr := (L : ℝ)) (q := 9 / 8) (s := s) (KG := KG 2 Cc 4) (KM := KM4 2 Cc)
    (Q := 2 * cNn * cSn * Q₀) (S := 2 * (L : ℝ) ^ 2 * S₀) hL1 (by norm_num)
    (by have : (32 : ℝ) + 16 < L := by exact_mod_cast hL
        norm_num; linarith)
    hs1 (KG_nonneg 2 (Cc := Cc) (by norm_num)) (KM4_nonneg 2 (Cc := Cc))
    (by positivity)
    (by positivity) (j := j₀) (n := n) ℓ wt κQ κS hℓ hwt (fun i _ _ => hℓq i) hw2 hsL hκQ hκS
  exact H1.trans H2

set_option maxHeartbeats 4000000 in
/-- **`kobs_hist_stepABL` at the top scale `j = N_h`** (`ValidAtL`). -/
theorem kobs_hist_stepABLT {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBoundsABL L R.A C₀ η ε₀ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hws : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤)
    {j₀ : ℕ} (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hjj : j₀ ≤ j) (hj : j = Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (ck m k : ℝ) (hck : 0 ≤ ck) (hm0 : 0 < m) (hk0 : 0 ≤ k)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hk8 : 8 * k ≤ ck * m)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤ ENNReal.ofReal m)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b) ≤
      ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m))
    (hKo : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).K X) ≤ ENNReal.ofReal k) :
    ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
      ENNReal.ofReal (R.A ^ (nb (j + 1) U - 2 ^ 2)) *
        oTo w (j + 1) (histS R (j + 1) t) ((obsHistFrom R P j₀ o₀ (j + 1) t).K U) ≤
      ENNReal.ofReal ((kθ0 L R.A C₀ η + C₁ * (2 + 2 * (8 * cx κ cT) + ck) *
          (cR R Λ cm C₂ * (t j).1)) * (8 * k) +
        kB (kθ0 L R.A C₀ η) C₁ (8 * cx κ cT) * (cR R Λ cm C₂ * (t j).1) ^ 2 * m) := by
  have hℓ : 0 < R.ℓ := Fact.out
  subst hj
  have hVj := hVL.2
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 j hV t
  set st := rawHist R j t with hst
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H j le_rfl t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 j le_rfl
  set g := (t j).1 with hgdef
  set μ := (t j).2.1
  set x := (t j).2.2
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hg1 : g ≤ 1 := hgε.trans H.hε1
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
  have hg3 : g ^ 3 ≤ ε * g ^ 2 := by
    rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
  have hdd : ‖x.1‖ ≤ g ^ 2 := by
    have := H.h3; nlinarith [mul_le_mul_of_nonneg_left hg3 H.hcx, sq_nonneg g]
  have hv : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ cV R Λ cm * g := by
    unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu Λ cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  set r := cR R Λ cm C₂ * g with hr
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ r := by
    refine hv.trans ?_; rw [hr]; unfold cR; nlinarith
  have hwr : cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ r ^ 2 := by
    rw [hr]; unfold cR
    have h1 : cW R Λ cm C₂ + 1 ≤ (cV R Λ cm + cW R Λ cm C₂ + 2) ^ 2 := by nlinarith
    nlinarith [sq_nonneg g]
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  -- the radius
  have hcR1 : 1 ≤ cR R Λ cm C₂ := by unfold cR; linarith
  have hgr : g ≤ r := by rw [hr]; nlinarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrε : r ≤ cR R Λ cm C₂ * ε := mul_le_mul_of_nonneg_left hgε (by linarith)
  have hr1 : r ≤ 1 := hrε.trans hε1
  have hcx := H.hcx
  have hbr : 8 * ‖x.2‖ ≤ 8 * cx κ cT * r ^ 3 := by
    have : g ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hg.le hgr 3
    nlinarith [mul_le_mul_of_nonneg_left this hcx]
  have hr3 : r ^ 3 ≤ r := by
    have : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1
    nlinarith
  have hεk' : 8 * ‖x.2‖ + r / m * (8 * k) ≤ ε₀ := by
    have h1 : r / m * (8 * k) ≤ ck * r := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hm0]
      have := mul_le_mul_of_nonneg_left hk8 hr0.le
      calc r * (8 * k) ≤ r * (ck * m) := this
        _ = ck * r * m := by ring
    have h2 : 8 * ‖x.2‖ ≤ 8 * cx κ cT * r := hbr.trans
      (mul_le_mul_of_nonneg_left hr3 (by positivity))
    have h3 : (8 * cx κ cT + ck) * r ≤ (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) :=
      mul_le_mul_of_nonneg_left hrε (by positivity)
    nlinarith
  -- the observable invariants
  have hval : ∀ i < j + 1, ValidCore R i ∧ RawInv R i (rawHist R i t) := fun i hi =>
    hist_validL R hV hVL t i (by omega)
  have hloc := obsLocInv_histFrom' R P hl0 t hjj fun i _ hi => hval i (by omega)
  have hsym := obsSymInv_histFrom' R P hs0 t hjj fun i _ hi => hval i (by omega)
  have hanc := obsAnchInv_histFrom' R P ha0 t hjj
  have hobs := obsHistFrom_isObs (R := R) (P := P) (j := j₀) h0 t j
  rw [obsHistFrom_succ hjj]
  exact hKB N R j hVj st HI g μ _ _ (rawD_mem R _ _) (rawK_mem R _ _) hmN hg.le
    (cZ R * g) hz hy hη hηs c P w hws hwa hwb hwab (obsHistFrom R P j₀ o₀ j t) hobs hloc hsym hanc
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r m k (8 * cx κ cT) ck (by positivity) (norm_nonneg _)
    (norm_nonneg _) hr0 hm0 hk0 (by positivity) hck hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x))
    (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr hr1 (hrε.trans hεε) hbr hk8 hεk' hVo hWo hKo

/-- **`wobs_hist_stepAB` at the top scale `j = N_h`** (`ValidAtL`). -/
theorem wobs_hist_stepABT {Kw C₁ ε₁ : ℝ} (hWB : WObsBoundsAB L Kw C₁ ε₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hws : w.Sub)
    {j₀ : ℕ} (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hjj : j₀ ≤ j) (hj : j = Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hε₁ : cR R Λ cm C₂ * ε ≤ ε₁) (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b) ≤ ENNReal.ofReal mW) :
    ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      oTo w (j + 1) (histS R (j + 1) t) ((obsHistFrom R P j₀ o₀ (j + 1) t).W c') ≤
        ENNReal.ofReal ((Kw / L + C₁ * (cR R Λ cm C₂ * (t j).1)) * mW +
          C₁ * (cR R Λ cm C₂ * (t j).1) * mV) := by
  subst hj
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, hWl, hDd, hvr, hwr, hr0, hrε, hcw, -, -⟩ :=
    hist_rawL R hSB hV hm hβ hδ1 H hVL t ht
  have hval : ∀ i < j + 1, ValidCore R i ∧ RawInv R i (rawHist R i t) := fun i hi =>
    hist_validL R hV hVL t i (by omega)
  have hloc := obsLocInv_histFrom' R P hl0 t hjj fun i _ hi => hval i (by omega)
  have hsym := obsSymInv_histFrom' R P hs0 t hjj fun i _ hi => hval i (by omega)
  have hanc := obsAnchInv_histFrom' R P ha0 t hjj
  have hobs := obsHistFrom_isObs (R := R) (P := P) (j := j₀) h0 t j
  rw [obsHistFrom_succ hjj]
  exact hWB N R j hVc (rawHist R j t) HI (t j).1 (t j).2.1 _ _ (rawD_mem R _ _) (rawK_mem R _ _)
    hmN hg _ hz hy hη hηs c P w hws (obsHistFrom R P j₀ o₀ j t) hobs hloc hsym hanc _ _ _
    mV mW (by positivity) (norm_nonneg _) hr0.le (hrε.trans hε₁) hmV hmW hWl hDd hvr hwr hVo hWo

end Hist

end

end PtCorr2
