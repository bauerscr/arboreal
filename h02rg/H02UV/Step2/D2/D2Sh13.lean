import Step2.D2.D2Sh12

/-!
# The sharp `g²` coefficient (HV, sharp form)

For `j ≥ 1`, with the dressed tadpole `T̃_j = 16 (C'_{j+1}(e₀) - C'_{j+1}(0)) ŵ'_j(0)` as an explicit
term:

  `|Re(2c - (q̃ + ∑_{k<j} b̃_k) + T̃_j) - 3 log L/(2π)| ≤ C₀ (L^{-2j} + m² L^{2(j+1)}) + E₁ max_{i≤j} |ζ_i|`,

`C₀` absolute.
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann DressedFRD DressedFRD.Data

variable {L N : ℕ} [NeZero L]

/-- The dressed tadpole `T̃_j = 16 (C'_{j+1}(e₀) - C'_{j+1}(0)) ŵ'_j(0)`. -/
def tadTil (D : Data 2 (L ^ N)) (j : ℕ) : ℂ :=
  16 * (DressedFRD.kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Lam 2 L N) -
    DressedFRD.kern (Cp D (j + 1)) 0) * wp D j 0

/-- The sharp constant `C₀`. -/
def C0sh : ℝ := 2 * ((2 * Real.pi)⁻¹ ^ 2 * (ErrC1 + 2 * ErrB)) + Csh

set_option maxHeartbeats 2000000 in
/-- **HV, sharp form.** -/
theorem HV_sharp : ∀ (L : ℕ) [NeZero L], 49 ≤ L →
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ E1 : ℝ, 0 ≤ E1 ∧
    ∀ (N : ℕ) (msq : ℝ) (ζ : ℕ → ℂ), 1 ≤ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
      (∀ i, ‖ζ i‖ ≤ ζbar) → ∀ j : ℕ, 1 ≤ j → j + 1 < N → ∀ ℓ : ℝ, 0 ≤ ℓ →
      (∀ i ≤ j, GoodCov2 i ℓ (DressedFRD.kmat ((dData L N msq ζ).Gint i))) → ∀ κ : ℕ → Coup,
      |(2 * cTil (dData L N msq ζ) j -
          (qTil (dData L N msq ζ) κ j + ∑ k ∈ range j, bTil (dData L N msq ζ) κ j k) +
          tadTil (dData L N msq ζ) j).re - 3 * (Real.log L / (2 * Real.pi))| ≤
        C0sh * ((((L : ℝ) ^ j) ^ 2)⁻¹ + msq * ((L : ℝ) ^ (j + 1)) ^ 2) +
          E1 * (dData L N msq ζ).Mz (j + 1) := by
  intro L _ hL
  have hpi := Real.pi_pos
  obtain ⟨ζbar, hζ, hζ8, K, hK⟩ := thm_main_frd Pc (d := 2) le_rfl (q := 4) (by norm_num)
    (by omega : 7 ≤ L)
  obtain ⟨cS, hcS, hS⟩ := frd_stdFull Pc (d := 2) le_rfl (by omega : 7 ≤ L) (q := 4)
    (M := 4 + 2 + 1) le_rfl
  set K' := max K 0
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hKK : K ≤ K' := le_max_left _ _
  set E1d := 72 * (cS + K') ^ 2 + 112 / 3 * cS * K' +
    (L : ℝ) ^ 2 * (8 + 2 * (L : ℝ) ^ 2 + 4 * L) * (2 * cS + K') * K'
  have hE1d : 0 ≤ E1d := by positivity
  refine ⟨ζbar, hζ, 2 * K' + E1d, by positivity,
    fun N msq ζ hN hm hmN hζb j hj hjN ℓ hℓ hG κ => ?_⟩
  set D := dData L N msq ζ
  have hc : ∀ i < N, D.Concl 4 ζbar K i := (hK (L ^ N) N msq ζ hN rfl hm hmN).1 hζb
  have hclose : ∀ i, i + 1 < N →
      snorm (L : ℝ) 4 i (D.Z (i + 1) • D.Gint i - ofR (D.C (i + 1))) ≤ K' * D.Mz (i + 1) :=
    fun i hi => ((hc i (by omega)).close hi).trans
      (mul_le_mul_of_nonneg_right hKK (Mz_nonneg _))
  have hrange : ∀ i, i + 1 < N → 2 * rng (D.Gint i) < L ^ (i + 1) := fun i hi =>
    (hc i (by omega)).range hi
  have hS' : StdFull L N 4 (4 + 2 + 1) D.msq cS D.C := hS (L ^ N) N msq hN rfl hm
  have hCs : ∀ k π s m, D.C k (symmDual π s m) = D.C k m :=
    fun k π s m => frdC_symm Pc msq L N k π s m
  have hζ8' : ∀ i, ‖D.ζ i‖ ≤ 1 / 8 := fun i => (hζb i).trans hζ8
  have hZ : ∀ i, D.Z i ≠ 0 := Z_ne_zero (fun i => (hζ8' i).trans (by norm_num))
  have hL2 : 2 ≤ L := by omega
  have hL7 : 7 ≤ L := by omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hn : 2 * (L ^ (j + 1) + 4) < L ^ N := by
    have h1 : L ^ (j + 1) * L ≤ L ^ N := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) hjN
    have h2 : L ≤ L ^ (j + 1) := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : L ^ (j + 1) * 7 ≤ L ^ (j + 1) * L := Nat.mul_le_mul_left _ hL7
    omega
  set Mz := D.Mz (j + 1)
  have hMz0 : 0 ≤ Mz := Mz_nonneg _
  set I := (((L : ℝ) ^ j) ^ 2)⁻¹
  set M := msq * ((L : ℝ) ^ (j + 1)) ^ 2
  have hI : 0 ≤ I := by positivity
  have hM : 0 ≤ M := by positivity
  have hm1 := msq_le_one (by omega) hN hmN
  -- the pieces
  have P1 := past_sum_bubX D (by norm_num; omega) hjN hCs (fun k hk => hrange k (by omega)) hZ
    hℓ hG κ
  have hdress := bub_dress D hS' le_rfl hL2 hζ8' hK'0 hclose hrange hjN hn
  have hund := undressed_bubble hm (by omega) hjN hn
  rw [if_pos hj] at hund
  have hsharp := frakBT_sharp hL7 hj hjN hm hmN
  -- line 1, sharp
  set Cl := (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 + 2 * ErrB)
  have hCl : 0 ≤ Cl := by
    have : 0 ≤ ErrC1 := by
      rw [ErrC1]
      have := ErrA_nonneg; have := KH_nonneg; have := kap_pos; have := Ia_nonneg 3
      positivity
    have := ErrB_nonneg
    positivity
  have hline1 : ‖DressedFRD.kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Lam 2 L N) -
      ((Real.log L / (2 * Real.pi) : ℝ) : ℂ)‖ ≤ Cl * (I + M) + K' * Mz := by
    have hCp : Cp D (j + 1) = ofR (D.C (j + 1)) + (Cp D (j + 1) - ofR (D.C (j + 1))) := by abel
    rw [hCp, DressedFRD.kern_add]
    have h1 : DressedFRD.kern (ofR (D.C (j + 1))) (dirVec (Sum.inl 0) : Lam 2 L N) =
        ((FRD.Cj Pc msq (L : ℝ) (j + 1) (unitT 0 : Grassmann.Torus 2 (L ^ N)) 0 : ℝ) : ℂ) :=
      kern_ofR_frdC hjN _
    have h2 : ‖DressedFRD.kern (Cp D (j + 1) - ofR (D.C (j + 1))) (dirVec (Sum.inl 0) : Lam 2 L N)‖ ≤
        K' * Mz := by
      have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
      refine (norm_kern_le_snorm hL0 4 j _ _).trans ?_
      have := hclose j hjN
      simpa [Cp] using this
    have hn' := pow_half_lt (L := L) (N := N) (j := j) (by omega) hjN
    have h3 := Cj_succ_e1_value hm.le hm1 hL1 hj (unitT 0 : Grassmann.Torus 2 (L ^ N)) 0
      (lift_e1 _) hn'
    have h4 : (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 / ((L : ℝ) ^ j) ^ 2 +
        ErrB * msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2)) ≤ Cl * (I + M) := by
      have hE1 : 0 ≤ ErrC1 := by
        rw [ErrC1]
        have := ErrA_nonneg; have := KH_nonneg; have := kap_pos; have := Ia_nonneg 3
        positivity
      have hEB := ErrB_nonneg
      have hjj : ((L : ℝ) ^ j) ^ 2 ≤ ((L : ℝ) ^ (j + 1)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 (by omega)) 2
      have e1 : ErrC1 / ((L : ℝ) ^ j) ^ 2 = ErrC1 * I := by rw [div_eq_mul_inv]
      have e2 : ErrB * msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2) ≤ 2 * ErrB * M := by
        simp only [M]
        have : msq * ((L : ℝ) ^ j) ^ 2 ≤ msq * ((L : ℝ) ^ (j + 1)) ^ 2 := by gcongr
        nlinarith
      rw [e1]
      have hp : 0 ≤ (2 * Real.pi)⁻¹ ^ 2 := by positivity
      calc (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 * I + ErrB * msq * (((L : ℝ) ^ j) ^ 2 +
            ((L : ℝ) ^ (j + 1)) ^ 2)) ≤ (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 * I + 2 * ErrB * M) := by
            gcongr
        _ ≤ (2 * Real.pi)⁻¹ ^ 2 * ((ErrC1 + 2 * ErrB) * (I + M)) := by
            gcongr
            have : 0 ≤ ErrC1 * M := by positivity
            have : 0 ≤ 2 * ErrB * I := by positivity
            nlinarith
        _ = Cl * (I + M) := by simp only [Cl]; ring
    rw [h1]
    calc _ = ‖(((FRD.Cj Pc msq (L : ℝ) (j + 1) (unitT 0 : Grassmann.Torus 2 (L ^ N)) 0 -
            Real.log L / (2 * Real.pi) : ℝ)) : ℂ) +
          DressedFRD.kern (Cp D (j + 1) - ofR (D.C (j + 1))) (dirVec (Sum.inl 0) : Lam 2 L N)‖ := by
          congr 1; push_cast; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (by rw [Complex.norm_real]; exact h3.trans h4) h2)
  -- assemble
  have hcTil : cTil D j = DressedFRD.kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Lam 2 L N) := by
    simp only [cTil, Cp, show j + 1 - 1 = j by omega, DressedFRD.kern_smul]; rfl
  have hsum : qTil D κ j + ∑ k ∈ range j, bTil D κ j k =
      D.Z (j + 1) ^ 2 * ((gFS D κ).betaQ j j 0 0 (eC 3) (eC 3) 3 +
        ∑ k ∈ range j, (gFS D κ).beta j k 0 0 (eC 3) (eC 3) 3) := by
    simp only [qTil, bTil, mul_add, mul_sum]
  rw [hcTil, hsum, P1]
  set A := cKer (L ^ (j + 1)) (wp D j)
  set B := cKer (L ^ (j + 1)) (Cp D (j + 1))
  set A0 := cKer (L ^ (j + 1)) (Cle D.C j)
  set B0 := cKer (L ^ (j + 1)) (ofR (D.C (j + 1)))
  set c := DressedFRD.kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Lam 2 L N)
  set ℓL : ℂ := ((Real.log L / (2 * Real.pi) : ℝ) : ℂ)
  have htad : tadTil D j = 16 * (c - DressedFRD.kern (Cp D (j + 1)) 0) * wp D j 0 := rfl
  rw [htad]
  set T16 := 16 * (c - DressedFRD.kern (Cp D (j + 1)) 0) * wp D j 0
  have hbub : -(2 * bubX A0 B0 + bubX B0 B0) - ℓL =
      frakBT L N msq ((L : ℝ) ^ (j + 1) / 2) - frakBT L N msq ((L : ℝ) ^ j / 2) - ℓL := by
    have : 2 * bubX A0 B0 + bubX B0 B0 = -frakBT L N msq ((L : ℝ) ^ (j + 1) / 2) +
        frakBT L N msq ((L : ℝ) ^ j / 2) := hund
    rw [this]; ring
  have hkey : 2 * c - (2 * bubX A B + bubX B B + T16) + T16 - 3 * ℓL =
      2 * (c - ℓL) + (-(2 * bubX A0 B0 + bubX B0 B0) - ℓL) -
        ((2 * bubX A B + bubX B B) - (2 * bubX A0 B0 + bubX B0 B0)) := by ring
  have hre : (2 * c - (2 * bubX A B + bubX B B + T16) + T16).re - 3 * (Real.log L / (2 * Real.pi)) =
      (2 * c - (2 * bubX A B + bubX B B + T16) + T16 - 3 * ℓL).re := by
    rw [Complex.sub_re]
    congr 1
    rw [show (3 : ℂ) * ℓL = ((3 * (Real.log L / (2 * Real.pi)) : ℝ) : ℂ) by
      simp only [ℓL]; push_cast; ring, Complex.ofReal_re]
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [hkey, hbub]
  calc ‖2 * (c - ℓL) + (frakBT L N msq ((L : ℝ) ^ (j + 1) / 2) - frakBT L N msq ((L : ℝ) ^ j / 2) - ℓL) -
        ((2 * bubX A B + bubX B B) - (2 * bubX A0 B0 + bubX B0 B0))‖
      ≤ 2 * ‖c - ℓL‖ + ‖frakBT L N msq ((L : ℝ) ^ (j + 1) / 2) - frakBT L N msq ((L : ℝ) ^ j / 2) - ℓL‖ +
        ‖(2 * bubX A B + bubX B B) - (2 * bubX A0 B0 + bubX B0 B0)‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add ?_ le_rfl)) le_rfl)
        rw [norm_mul, Complex.norm_ofNat]
    _ ≤ 2 * (Cl * (I + M) + K' * Mz) + (Csh * I + Csh * M) + E1d * Mz := by
        gcongr
    _ = C0sh * (I + M) + (2 * K' + E1d) * Mz := by unfold C0sh; simp only [Cl]; ring

end

end Step2
