import Step2.D2.D2HV10

/-!
# The dressed tadpole: (S0), (S1) for `C'` and `|z² T_j| ≤ 16 M₂ M₀ + E · M_z`

* `S1_dressed`: `|C'_{j+1}(e₀) - C'_{j+1}(0)| ≤ (M₂ + K M_z/2) L^{-2j}`;
* `S0_dressed`: `|ŵ'_j(0)| ≤ (M₀ + (18/7)(K + M₀) M_z) L^{2j}`;
* `tad_dressed`: `|16 (C'_{j+1}(e₀) - C'_{j+1}(0)) ŵ'_j(0)| ≤ 16 M₂ M₀ + Et · M_z`.
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann DressedFRD DressedFRD.Data

variable {L N : ℕ} [NeZero L]

local notation "Λ2" => Lam 2 L N

section Tad

variable (D : Data 2 (L ^ N)) {q M : ℕ} {cS K M₀ M₂ : ℝ}

/-- **(S1) for the dressed covariance.** -/
theorem S1_dressed (hq : 4 ≤ q) (hK : 0 ≤ K)
    (hC : ∀ k π s m, D.C k (symmDual π s m) = D.C k m)
    (hclose : ∀ i, i + 1 < N →
      snorm (L : ℝ) q i (D.Z (i + 1) • D.Gint i - ofR (D.C (i + 1))) ≤ K * D.Mz (i + 1))
    {j : ℕ} (hjN : j + 1 < N)
    (hS1 : ‖kern (ofR (D.C (j + 1))) (dirVec (Sum.inl 0) : Λ2) - kern (ofR (D.C (j + 1))) 0‖ ≤
      M₂ / ((L : ℝ) ^ j) ^ 2) :
    ‖kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Λ2) - kern (Cp D (j + 1)) 0‖ ≤
      (M₂ + K * D.Mz (j + 1) / 2) / ((L : ℝ) ^ j) ^ 2 := by
  set δ := Cp D (j + 1) - ofR (D.C (j + 1))
  have hCp : Cp D (j + 1) = ofR (D.C (j + 1)) + δ := by simp [δ]
  have hsymC : ofR (D.C (j + 1)) ∈ symSub := ofR_symMem (hC (j + 1))
  have hsymδ : δ ∈ symSub := by
    refine Subring.sub_mem _ ?_ hsymC
    simp only [Cp, show j + 1 - 1 = j by omega]
    exact smul_symMem _ (DData.Gint_symMem hC j)
  have hd := dopB_of_snorm (L := L) (N := N) hq (hclose j hjN)
  have hdA := hd (Ai 0) (by rw [mabs_Ai]; norm_num) 0
  rw [mabs_Ai] at hdA
  have hδe := kern_e0_sub_zero hsymδ
  rw [hCp, kern_add, kern_add]
  have e : kern (ofR (D.C (j + 1))) (dirVec (Sum.inl 0) : Λ2) + kern δ (dirVec (Sum.inl 0)) -
      (kern (ofR (D.C (j + 1))) 0 + kern δ 0) =
      (kern (ofR (D.C (j + 1))) (dirVec (Sum.inl 0) : Λ2) - kern (ofR (D.C (j + 1))) 0) +
        (kern δ (dirVec (Sum.inl 0)) - kern δ 0) := by ring
  rw [e, hδe]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, show ‖-(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have hρ : 0 < ((L : ℝ) ^ j) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hδdef : δ = D.Z (j + 1) • D.Gint j - ofR (D.C (j + 1)) := by simp [δ, Cp]
  calc _ ≤ M₂ / ((L : ℝ) ^ j) ^ 2 + 1 / 2 * (K * D.Mz (j + 1) / ((L : ℝ) ^ j) ^ 2) := by
        gcongr
        rw [hδdef]; exact hdA
    _ = _ := by ring

/-- **(S0) for the dressed past.** -/
theorem S0_dressed (hS : StdFull L N q M D.msq cS D.C) (hq : 4 ≤ q) (hL : 2 ≤ L)
    (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 8) (hK : 0 ≤ K)
    (hclose : ∀ i, i + 1 < N →
      snorm (L : ℝ) q i (D.Z (i + 1) • D.Gint i - ofR (D.C (i + 1))) ≤ K * D.Mz (i + 1))
    (hrange : ∀ i, i + 1 < N → 2 * rng (D.Gint i) < L ^ (i + 1))
    {j : ℕ} (hjN : j + 1 < N) (hM₀ : 0 ≤ M₀)
    (hS0 : ∀ k ≤ j, ∀ m, 0 ≤ ∑ k' ∈ Icc 1 k, D.C k' m ∧
      ∑ k' ∈ Icc 1 k, D.C k' m ≤ M₀ * ((L : ℝ) ^ k) ^ 2) :
    ‖wp D j 0‖ ≤ ((L : ℝ) ^ j) ^ 2 * (M₀ + 18 / 7 * (K + M₀) * D.Mz (j + 1)) := by
  set Lr : ℝ := (L : ℝ)
  have hL0 : 0 < Lr := by simp only [Lr]; exact_mod_cast (by omega : 0 < L)
  have hL2 : (2 : ℝ) ≤ Lr := by simp only [Lr]; exact_mod_cast hL
  have hζ2 : ∀ i, ‖D.ζ i‖ ≤ 1 / 2 := fun i => (hζ i).trans (by norm_num)
  set Mz := D.Mz (j + 1)
  have hMz0 : 0 ≤ Mz := Mz_nonneg _
  have hMz : Mz ≤ 1 / 8 := Mz_le (by norm_num) fun i _ => hζ i
  set δ : ℕ → Sym 2 (L ^ N) := fun k => Cp D k - ofR (D.C k)
  set ρ : ℕ → ℂ := fun k => D.Z (j + 1) / D.Z k
  have hdec : wp D j = Cle D.C j + ∑ k ∈ Icc 1 j, (ρ k • δ k + (ρ k - 1) • ofR (D.C k)) := by
    have : wp D j - Cle D.C j = ∑ k ∈ Icc 1 j, (ρ k • δ k + (ρ k - 1) • ofR (D.C k)) := by
      simp only [wp, Cle, ← sum_sub_distrib]
      refine sum_congr rfl fun k _ => ?_
      simp only [δ, ρ, smul_sub, sub_smul, one_smul]; abel
    rw [← this]; abel
  have hρb : ∀ k ∈ Icc 1 j, ‖ρ k‖ ≤ (1 + Mz) ^ (j + 1 - k) ∧
      ‖ρ k - 1‖ ≤ ((j + 1 - k : ℕ) : ℝ) * Mz * (1 + Mz) ^ (j + 1 - k) := by
    intro k hk
    have hk' := mem_Icc.1 hk
    have e := Z_ratio_eq D hζ2 (k := k) (j := j) (by omega)
    have hb' := prod_one_add_bounds (Ico k (j + 1)) D.ζ hMz0
      (fun i hi => norm_le_Mz (mem_Ico.1 hi).2)
    rw [Nat.card_Ico] at hb'
    simp only [ρ]
    rw [e]
    exact ⟨hb'.1, hb'.2.trans (one_add_pow_sub_one_le hMz0 _)⟩
  -- the undressed zero mode
  have hCle : ‖Cle D.C j 0‖ ≤ M₀ * (Lr ^ j) ^ 2 := by
    have e : Cle D.C j 0 = ((∑ k ∈ Icc 1 j, D.C k 0 : ℝ) : ℂ) := by
      simp [Cle, ofR, Finset.sum_apply]
    rw [e, Complex.norm_real, Real.norm_of_nonneg (hS0 j le_rfl 0).1]
    exact (hS0 j le_rfl 0).2
  -- the dressing terms
  have hterm : ∀ k ∈ Icc 1 j, ‖(ρ k • δ k + (ρ k - 1) • ofR (D.C k)) 0‖ ≤
      (Lr ^ j) ^ 2 * (9 / 8 * (9 / 16) ^ (j - k) * ((K + M₀) * Mz)) := by
    intro k hk
    have hk' := mem_Icc.1 hk
    have hkN : k < N := by omega
    obtain ⟨r1, r2⟩ := hρb k hk
    obtain ⟨c1, c2⟩ := coef_bound hL2 hMz0 hMz hk'.2
    -- `δ_k(0)`
    have hδ0 : ‖δ k 0‖ ≤ (Lr ^ k) ^ 2 * (K * Mz) := by
      rw [← sum_kern_eq (δ k)]
      refine (norm_sum_le _ _).trans ?_
      have hrng : 2 * rng (δ k) < L ^ k := by
        have h1 := hrange (k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega] at h1
        have h2 := hS.base.range k hk'.1 hkN
        have h3 : rng (δ k) ≤ max (rng (Cp D k)) (rng (ofR (D.C k))) := rng_sub_le _ _
        have h4 : rng (Cp D k) ≤ rng (D.Gint (k - 1)) := rng_smul_le _ _
        omega
      refine kern_sum_le hrng fun x => ?_
      have hs := hclose (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at hs
      refine (norm_kern_le_snorm hL0 q (k - 1) _ x).trans (hs.trans ?_)
      gcongr; exact Mz_mono (by omega)
    -- `C_k(0)`
    have hC0 : ‖ofR (D.C k) 0‖ ≤ M₀ * (Lr ^ k) ^ 2 := by
      rw [ofR, Complex.norm_real, Real.norm_of_nonneg (hS.base.nonneg k 0)]
      refine le_trans ?_ (hS0 k (by omega) 0).2
      exact single_le_sum (f := fun k' => D.C k' 0) (fun i _ => hS.base.nonneg i 0)
        (mem_Icc.2 ⟨hk'.1, le_rfl⟩)
    have hq0 : 0 ≤ (Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹ := by positivity
    have e1 : ‖ρ k‖ * ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹) ≤ 9 / 8 * (9 / 16) ^ (j - k) :=
      (mul_le_mul_of_nonneg_right r1 hq0).trans c2
    have e2 : ‖ρ k - 1‖ * ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹) ≤ 9 / 8 * (9 / 16) ^ (j - k) * Mz := by
      refine (mul_le_mul_of_nonneg_right r2 hq0).trans ?_
      calc ((j + 1 - k : ℕ) : ℝ) * Mz * (1 + Mz) ^ (j + 1 - k) *
            ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹) =
            Mz * (((j + 1 - k : ℕ) : ℝ) * (1 + Mz) ^ (j + 1 - k) *
              ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹)) := by ring
        _ ≤ Mz * (9 / 8 * (9 / 16) ^ (j - k)) := mul_le_mul_of_nonneg_left c1 hMz0
        _ = _ := by ring
    have hj2 : 0 < (Lr ^ j) ^ 2 := by positivity
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc ‖ρ k * δ k 0 + (ρ k - 1) * ofR (D.C k) 0‖ ≤ ‖ρ k‖ * ‖δ k 0‖ + ‖ρ k - 1‖ * ‖ofR (D.C k) 0‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
      _ ≤ ‖ρ k‖ * ((Lr ^ k) ^ 2 * (K * Mz)) + ‖ρ k - 1‖ * (M₀ * (Lr ^ k) ^ 2) := by gcongr
      _ = (Lr ^ j) ^ 2 * ((‖ρ k‖ * ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹)) * (K * Mz) +
            (‖ρ k - 1‖ * ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹)) * M₀) := by
          field_simp
      _ ≤ (Lr ^ j) ^ 2 * ((9 / 8 * (9 / 16) ^ (j - k)) * (K * Mz) +
            (9 / 8 * (9 / 16) ^ (j - k) * Mz) * M₀) := by gcongr
      _ = _ := by ring
  rw [hdec, Pi.add_apply, Finset.sum_apply]
  refine (norm_add_le _ _).trans ?_
  have hg := geom_Icc_le j
  calc ‖Cle D.C j 0‖ + ‖∑ c ∈ Icc 1 j, (ρ c • δ c + (ρ c - 1) • ofR (D.C c)) 0‖
      ≤ M₀ * (Lr ^ j) ^ 2 + ∑ k ∈ Icc 1 j, (Lr ^ j) ^ 2 * (9 / 8 * (9 / 16) ^ (j - k) * ((K + M₀) * Mz)) :=
        add_le_add hCle ((norm_sum_le _ _).trans (sum_le_sum hterm))
    _ = M₀ * (Lr ^ j) ^ 2 + (Lr ^ j) ^ 2 * (9 / 8 * ((K + M₀) * Mz)) *
          ∑ k ∈ Icc 1 j, ((9 : ℝ) / 16) ^ (j - k) := by
        rw [mul_sum]; congr 1; refine sum_congr rfl fun k _ => by ring
    _ ≤ M₀ * (Lr ^ j) ^ 2 + (Lr ^ j) ^ 2 * (9 / 8 * ((K + M₀) * Mz)) * (16 / 7) := by
        have : 0 ≤ (Lr ^ j) ^ 2 * (9 / 8 * ((K + M₀) * Mz)) := by positivity
        gcongr
    _ = _ := by ring

/-- **The dressed tadpole.** -/
theorem tad_dressed (hS : StdFull L N q M D.msq cS D.C) (hq : 4 ≤ q) (hL : 2 ≤ L)
    (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 8) (hK : 0 ≤ K)
    (hC : ∀ k π s m, D.C k (symmDual π s m) = D.C k m)
    (hclose : ∀ i, i + 1 < N →
      snorm (L : ℝ) q i (D.Z (i + 1) • D.Gint i - ofR (D.C (i + 1))) ≤ K * D.Mz (i + 1))
    (hrange : ∀ i, i + 1 < N → 2 * rng (D.Gint i) < L ^ (i + 1))
    {j : ℕ} (hjN : j + 1 < N) (hM₀ : 0 ≤ M₀) (hM₂ : 0 ≤ M₂)
    (hS0 : ∀ k ≤ j, ∀ m, 0 ≤ ∑ k' ∈ Icc 1 k, D.C k' m ∧
      ∑ k' ∈ Icc 1 k, D.C k' m ≤ M₀ * ((L : ℝ) ^ k) ^ 2)
    (hS1 : ‖kern (ofR (D.C (j + 1))) (dirVec (Sum.inl 0) : Λ2) - kern (ofR (D.C (j + 1))) 0‖ ≤
      M₂ / ((L : ℝ) ^ j) ^ 2) :
    ‖16 * (kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Λ2) - kern (Cp D (j + 1)) 0) * wp D j 0‖ ≤
      16 * M₂ * M₀ + 16 * (M₂ * (18 / 7 * (K + M₀)) + K * M₀ / 2 + K * (18 / 7 * (K + M₀)) / 16) *
        D.Mz (j + 1) := by
  have h1 := S1_dressed D hq hK hC hclose hjN hS1
  have h0 := S0_dressed D hS hq hL hζ hK hclose hrange hjN hM₀ hS0
  set Mz := D.Mz (j + 1)
  have hMz0 : 0 ≤ Mz := Mz_nonneg _
  have hMz : Mz ≤ 1 / 8 := Mz_le (by norm_num) fun i _ => hζ i
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hj2 : 0 < ((L : ℝ) ^ j) ^ 2 := by positivity
  rw [norm_mul, norm_mul, Complex.norm_ofNat]
  calc 16 * ‖kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Λ2) - kern (Cp D (j + 1)) 0‖ * ‖wp D j 0‖
      ≤ 16 * ((M₂ + K * Mz / 2) / ((L : ℝ) ^ j) ^ 2) *
          (((L : ℝ) ^ j) ^ 2 * (M₀ + 18 / 7 * (K + M₀) * Mz)) := by gcongr
    _ = 16 * ((M₂ + K * Mz / 2) * (M₀ + 18 / 7 * (K + M₀) * Mz)) := by field_simp
    _ ≤ _ := by
        have hKM : 0 ≤ K * (18 / 7 * (K + M₀)) := by positivity
        have hsq : Mz * Mz ≤ Mz / 8 := by nlinarith
        nlinarith [mul_nonneg hKM hMz0, mul_nonneg (mul_nonneg hK hM₀) hMz0,
          mul_nonneg hM₂ hMz0]

end Tad

end

end Step2
