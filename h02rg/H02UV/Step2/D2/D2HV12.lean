import Step2.D2.D2HV11

/-!
# (HV): the `g²` coefficient of the normalised flow, `prop:d2` in assembled form

For the concrete dressed data `D = ⟨L, N, m², frdC Pc m² L N, ζ⟩`, the flow sequence with
`C_k = kmat Γ^int_k`, `s ≡ 1` (`gFS`), `z = Z_{j+1}`, `i₀ = 0`:

  `q̃ = z² q_{j,j}`, `b̃_k = z² b_{j,k}`, `c = z C_j(e₀, 0) = C'_{j+1}(e₀, 0)`,

**(HV)** `|Re(2c - (q̃ + ∑_{k<j} b̃_k)) - 3 log L/(2π)| ≤ E₀ + E₁ max_{i ≤ j} |ζ_i|`

for all `j` with `j + 1 < N` (including `j = 0`), with `E₀` independent of `L`.
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann DressedFRD DressedFRD.Data

/-- The concrete dressed data. -/
abbrev dData (L N : ℕ) (msq : ℝ) (ζ : ℕ → ℂ) : Data 2 (L ^ N) := ⟨L, N, msq, frdC Pc msq L N, ζ⟩

variable {L N : ℕ} [NeZero L]

/-- The flow sequence with `C_k = kmat Γ^int_k` and `s ≡ 1`. -/
abbrev gFS (D : Data 2 (L ^ N)) (κ : ℕ → Coup) : FlowSeq 2 L N :=
  ⟨fun k => DressedFRD.kmat (D.Gint k), fun _ => 1, κ⟩

/-- `q̃ = z² q_{j,j}`. -/
def qTil (D : Data 2 (L ^ N)) (κ : ℕ → Coup) (j : ℕ) : ℂ :=
  D.Z (j + 1) ^ 2 * (gFS D κ).betaQ j j 0 0 (eC 3) (eC 3) 3

/-- `b̃_k = z² b_{j,k}`. -/
def bTil (D : Data 2 (L ^ N)) (κ : ℕ → Coup) (j k : ℕ) : ℂ :=
  D.Z (j + 1) ^ 2 * (gFS D κ).beta j k 0 0 (eC 3) (eC 3) 3

/-- `c = z C_j(e₀, 0) = C'_{j+1}(e₀, 0)`. -/
def cTil (D : Data 2 (L ^ N)) (j : ℕ) : ℂ :=
  D.Z (j + 1) * DressedFRD.kern (D.Gint j) (unitT 0 : Lam 2 L N)

/-- The `L`-independent line-1 constant. -/
theorem line1_undressed : ∃ ELine : ℝ, 0 ≤ ELine ∧ ∀ (L N : ℕ) [NeZero L], 7 ≤ L →
    ∀ msq : ℝ, 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → ∀ j : ℕ, j + 1 < N →
      |FRD.Cj Pc msq (L : ℝ) (j + 1) (unitT 0 : Grassmann.Torus 2 (L ^ N)) 0 -
        Real.log L / (2 * Real.pi)| ≤ ELine := by
  obtain ⟨E10, hE10, hC1⟩ := C1_e1_value
  have hpi := Real.pi_pos
  have hE1 : 0 ≤ ErrC1 := by
    rw [ErrC1]
    have := ErrA_nonneg; have := KH_nonneg; have := kap_pos; have := Ia_nonneg 3
    positivity
  have hEB := ErrB_nonneg
  refine ⟨E10 + (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 + 8 * ErrB), by positivity,
    fun L N _ hL msq hm hmN j hjN => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hm1 := msq_le_one (by omega) (by omega) hmN
  have hmT := msq_mul_sq_le (L := L) (N := N) (j := j) (by omega) hjN hm.le hmN
  have hn' := pow_half_lt (L := L) (N := N) (j := j) (by omega) hjN
  have hp : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    have e : (FRD.Cj Pc msq (L : ℝ) (0 + 1) :
        Matrix (Grassmann.Torus 2 (L ^ N)) (Grassmann.Torus 2 (L ^ N)) ℝ) =
        FRD.cov Pc msq (Set.Ioc 0 ((L : ℝ) / 2)) := by
      simp [FRD.Cj, FRD.lowEnd]
    rw [e]
    have hmL : msq * (L : ℝ) ^ 2 ≤ 4 := by
      have : msq * ((L : ℝ) ^ (0 + 1) / 2) ^ 2 = msq * (L : ℝ) ^ 2 / 4 := by ring
      linarith
    have := hC1 (L ^ N) (L : ℝ) msq hL1 hm hm1 hmL (by push_cast at hn' ⊢; simpa using hn')
    have h2 : 0 ≤ (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 + 8 * ErrB) := by positivity
    linarith
  · have h := Cj_succ_e1_value hm.le hm1 hL1 (by omega : 1 ≤ j) (unitT 0) 0 (lift_e1 _) hn'
    refine h.trans ?_
    have hLj : (1 : ℝ) ≤ ((L : ℝ) ^ j) ^ 2 := one_le_pow₀ (one_le_pow₀ hL1)
    have h1 : ErrC1 / ((L : ℝ) ^ j) ^ 2 ≤ ErrC1 := div_le_self hE1 hLj
    have h2 : msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2) ≤ 8 := by
      have e : msq * ((L : ℝ) ^ (j + 1) / 2) ^ 2 = msq * ((L : ℝ) ^ (j + 1)) ^ 2 / 4 := by ring
      have h3 : ((L : ℝ) ^ j) ^ 2 ≤ ((L : ℝ) ^ (j + 1)) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 (by omega)) 2
      nlinarith
    have h3 : ErrB * msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2) ≤ 8 * ErrB := by
      calc ErrB * msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2) =
          ErrB * (msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2)) := by ring
        _ ≤ ErrB * 8 := mul_le_mul_of_nonneg_left h2 hEB
        _ = 8 * ErrB := by ring
    have : (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 / ((L : ℝ) ^ j) ^ 2 +
        ErrB * msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2)) ≤
        (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 + 8 * ErrB) := by gcongr
    linarith

/-- **(HV).** -/
theorem HV : ∃ E0 : ℝ, 0 ≤ E0 ∧ ∀ (L : ℕ) [NeZero L], 49 ≤ L →
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ E1 : ℝ, 0 ≤ E1 ∧
    ∀ (N : ℕ) (msq : ℝ) (ζ : ℕ → ℂ), 1 ≤ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
      (∀ i, ‖ζ i‖ ≤ ζbar) → ∀ j : ℕ, j + 1 < N → ∀ ℓ : ℝ, 0 ≤ ℓ →
      (∀ i ≤ j, GoodCov2 i ℓ (DressedFRD.kmat ((dData L N msq ζ).Gint i))) → ∀ κ : ℕ → Coup,
      |(2 * cTil (dData L N msq ζ) j -
          (qTil (dData L N msq ζ) κ j + ∑ k ∈ range j, bTil (dData L N msq ζ) κ j k)).re -
        3 * (Real.log L / (2 * Real.pi))| ≤ E0 + E1 * (dData L N msq ζ).Mz (j + 1) := by
  obtain ⟨M₂, hM₂0, hS1⟩ := first_diff_le
  obtain ⟨M₀, hM₀0, hS0⟩ := zmode_le
  obtain ⟨ELine, hEL, hline⟩ := line1_undressed
  have hpi := Real.pi_pos
  have hCB := CB0_nonneg
  have hl2 : 0 ≤ Real.log 2 / (2 * Real.pi) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); positivity
  refine ⟨2 * ELine + (2 * CB0 + Real.log 2 / (2 * Real.pi)) + 16 * M₂ * M₀, by positivity,
    fun L _ hL => ?_⟩
  obtain ⟨ζbar, hζ, hζ8, K, hK⟩ := thm_main_frd Pc (d := 2) le_rfl (q := 4) (by norm_num)
    (by omega : 7 ≤ L)
  obtain ⟨cS, hcS, hS⟩ := frd_stdFull Pc (d := 2) le_rfl (by omega : 7 ≤ L) (q := 4)
    (M := 4 + 2 + 1) le_rfl
  set K' := max K 0
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hKK : K ≤ K' := le_max_left _ _
  set E1d := 72 * (cS + K') ^ 2 + 112 / 3 * cS * K' +
    (L : ℝ) ^ 2 * (8 + 2 * (L : ℝ) ^ 2 + 4 * L) * (2 * cS + K') * K'
  set Et := 16 * (M₂ * (18 / 7 * (K' + M₀)) + K' * M₀ / 2 + K' * (18 / 7 * (K' + M₀)) / 16)
  have hE1d : 0 ≤ E1d := by positivity
  have hEt : 0 ≤ Et := by positivity
  refine ⟨ζbar, hζ, 2 * K' + E1d + Et, by positivity,
    fun N msq ζ hN hm hmN hζb j hjN ℓ hℓ hG κ => ?_⟩
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
  -- the pieces
  have P1 := past_sum_bubX D (by norm_num; omega) hjN hCs (fun k hk => hrange k (by omega)) hZ
    hℓ hG κ
  have hdress := bub_dress D hS' le_rfl hL2 hζ8' hK'0 hclose hrange hjN hn
  have hbv := bubble_value hL7 hjN hm hmN
  have htad := tad_dressed D hS' le_rfl hL2 hζ8' hK'0 hCs hclose hrange hjN hM₀0 hM₂0
    (fun k hk m => hS0 L N hL2 msq hm k (by omega) m) (hS1 L N hL7 msq hm j hjN)
  -- line 1
  have hline1 : ‖kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Lam 2 L N) -
      ((Real.log L / (2 * Real.pi) : ℝ) : ℂ)‖ ≤ ELine + K' * Mz := by
    have hCp : Cp D (j + 1) = ofR (D.C (j + 1)) + (Cp D (j + 1) - ofR (D.C (j + 1))) := by abel
    rw [hCp, kern_add]
    have h1 : kern (ofR (D.C (j + 1))) (dirVec (Sum.inl 0) : Lam 2 L N) =
        ((FRD.Cj Pc msq (L : ℝ) (j + 1) (unitT 0 : Grassmann.Torus 2 (L ^ N)) 0 : ℝ) : ℂ) :=
      kern_ofR_frdC hjN _
    have h2 : ‖kern (Cp D (j + 1) - ofR (D.C (j + 1))) (dirVec (Sum.inl 0) : Lam 2 L N)‖ ≤
        K' * Mz := by
      have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
      refine (norm_kern_le_snorm hL0 4 j _ _).trans ?_
      have := hclose j hjN
      simpa [Cp] using this
    have h3 := hline L N hL7 msq hm hmN j hjN
    rw [h1]
    calc _ = ‖(((FRD.Cj Pc msq (L : ℝ) (j + 1) (unitT 0 : Grassmann.Torus 2 (L ^ N)) 0 -
            Real.log L / (2 * Real.pi) : ℝ)) : ℂ) +
          kern (Cp D (j + 1) - ofR (D.C (j + 1))) (dirVec (Sum.inl 0) : Lam 2 L N)‖ := by
          congr 1; push_cast; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (by rw [Complex.norm_real]; exact h3) h2)
  -- assemble
  have hcTil : cTil D j = kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Lam 2 L N) := by
    simp only [cTil, Cp, show j + 1 - 1 = j by omega, kern_smul]; rfl
  have hsum : qTil D κ j + ∑ k ∈ range j, bTil D κ j k =
      D.Z (j + 1) ^ 2 * ((gFS D κ).betaQ j j 0 0 (eC 3) (eC 3) 3 +
        ∑ k ∈ range j, (gFS D κ).beta j k 0 0 (eC 3) (eC 3) 3) := by
    simp only [qTil, bTil, mul_add, mul_sum]
  rw [hcTil, hsum, P1]
  set A := cKer (L ^ (j + 1)) (wp D j)
  set B := cKer (L ^ (j + 1)) (Cp D (j + 1))
  set A0 := cKer (L ^ (j + 1)) (Cle D.C j)
  set B0 := cKer (L ^ (j + 1)) (ofR (D.C (j + 1)))
  set T16 := 16 * (kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Lam 2 L N) -
    kern (Cp D (j + 1)) 0) * wp D j 0
  set c := kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Lam 2 L N)
  set ℓL : ℂ := ((Real.log L / (2 * Real.pi) : ℝ) : ℂ)
  have hkey : 2 * c - (2 * bubX A B + bubX B B + T16) - 3 * ℓL =
      2 * (c - ℓL) + (-(2 * bubX A0 B0 + bubX B0 B0) - ℓL) -
        ((2 * bubX A B + bubX B B) - (2 * bubX A0 B0 + bubX B0 B0)) - T16 := by ring
  have hre : (2 * c - (2 * bubX A B + bubX B B + T16)).re - 3 * (Real.log L / (2 * Real.pi)) =
      (2 * c - (2 * bubX A B + bubX B B + T16) - 3 * ℓL).re := by
    rw [Complex.sub_re]
    congr 1
    rw [show (3 : ℂ) * ℓL = ((3 * (Real.log L / (2 * Real.pi)) : ℝ) : ℂ) by
      simp only [ℓL]; push_cast; ring, Complex.ofReal_re]
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [hkey]
  calc ‖2 * (c - ℓL) + (-(2 * bubX A0 B0 + bubX B0 B0) - ℓL) -
        ((2 * bubX A B + bubX B B) - (2 * bubX A0 B0 + bubX B0 B0)) - T16‖
      ≤ 2 * ‖c - ℓL‖ + ‖-(2 * bubX A0 B0 + bubX B0 B0) - ℓL‖ +
        ‖(2 * bubX A B + bubX B B) - (2 * bubX A0 B0 + bubX B0 B0)‖ + ‖T16‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ le_rfl)) le_rfl)) le_rfl)
        rw [norm_mul, Complex.norm_ofNat]
    _ ≤ 2 * (ELine + K' * Mz) + (2 * CB0 + Real.log 2 / (2 * Real.pi)) + E1d * Mz +
        (16 * M₂ * M₀ + Et * Mz) := by
        gcongr
    _ = _ := by ring

end

end Step2