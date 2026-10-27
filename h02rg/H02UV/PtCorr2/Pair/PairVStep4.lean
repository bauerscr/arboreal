import PtCorr2.Pair.PairVStep2
import PtCorr2.Pair.PairVStep3
import PtCorr2.Obs.ObsFlow
import PtCorr2.Obs.ProdBdHist

/-!
# The `V`-step of the joint induction (4): the gradient/`M₄` size of `V_n(B)_{ab}` along the history

**`gradV_hist_le`**: along the history from `j₀` (anchored, `V_{j₀}(·)_{ab} = 0`), for `j₀ ≤ n ≤ N_h`
and every `n`-block `B`, the `γ_n` input of `hVo_of_coeffsP`:
`gradM4Sz_{a}(V_n(B)_{ab}) ≤ 4w_n((2K_G + 3q² + 2K_M)·2c_Nc_SQ₀ + (2K_G + 3 + 2K_M)·2L²S₀)`
(`q = 9/8`), from
* per-scale small-set sizes `‖K_i(X)_{ab}‖_{T_i(s_i)} ≤ w_iQ₀` (`i < n`, `X` small),
* per-scale `S` sizes `‖S_i(B_+)_{ab}‖_{T_{i+1}(s_{i+1})} ≤ w_iS₀`,
* doubling weights `w_i ≤ 2w_{i+1}`, a path `w` from `a` to `b` with `|w| ≤ 2|a−b|_∞`,
  `2|a−b|_∞ ≤ L^{j₀+1}`,
* the counting constants `c_S` (small sets containing a block), `c_N` (blocks `B` with `x ∈ B^□`)
  and the cutoff constant `C_c`.

Chain: `gradM4Sz_hVR_block_sizesD` (covariance differences from `GoodCov2` with `ℓ_C = s_{i+1}/4`,
`covDiff_le_path`), `m4X_hVR_mu_le` + `m4SrcX_le_sizes` (the `μ_i`), `kappaQ_le_count`,
`kappaS_le_count`, `gamma_budget`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

theorem histS_succ_le_q (hρ0 : 0 ≤ R.ρ) (hρ : R.ρ ≤ 1 / 8) (t : Flow2.Hist.Seq (Xs R)) (i : ℕ) :
    histS R (i + 1) t ≤ 9 / 8 * histS R i t := by
  have h := histS_ratio_le R hρ0 (by linarith) i t
  have hz : ‖zetaH R i t‖ ≤ R.ρ := absorb_le R hρ0 _ _
  have h1 : histS R (i + 1) t / histS R i t ≤ 9 / 8 :=
    (le_max_right _ _).trans (h.trans (by linarith))
  have h0 := histS_pos' R hρ0 hρ t i
  rw [div_le_iff₀ h0] at h1; linarith

set_option maxHeartbeats 4000000 in
/-- **The gradient/`M₄` size of `V_n(B)_{ab}` from uniform per-scale source sizes.** -/
theorem gradV_hist_le (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
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
    (t : Flow2.Hist.Seq (Xs R)) {n : ℕ} (hjn : j₀ ≤ n) (hn : n ≤ Nh)
    (ht : ∀ i ≤ n, Flow2.Hist.InDh Λ β δ κ cg cm cT ε i t)
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
    hist_vstep_facts R hSB hV hm hβ hδ1 H P o₀ hl0 hs0 ha0 t i hi (by omega) (ht i (by omega))
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

end Hist

end

end PtCorr2
