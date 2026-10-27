import Step2.D2.D2HV7

/-!
# Sharp single-scale inputs for the tadpole (`L`-independent constants)

For the concrete decomposition `C = frdC Pc msq L N`, `L ≥ 7`:

* `zero_mode_le` (S0, undressed): `0 ≤ C_{≤j}(0) ≤ M₀ L^{2j}`;
* `first_diff_le` (S1, undressed): `|C_{j+1}(e₀) - C_{j+1}(0)| ≤ M₂ L^{-2j}`;
* `kern_e0_sub_zero`: for an even kernel, `k(e₀) - k(0) = -½ ∇^{A₀} k(0)`.

`M₀`, `M₂` depend only on the family `Pc` (not on `L`, `N`, `msq`, `j`).
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann DressedFRD DressedFRD.Data

variable {L N : ℕ} [NeZero L]

local notation "Λ2" => Lam 2 L N

/-- For an invariant symbol: `k(e₀) - k(0) = -½ ∇^{A₀} k(0)`. -/
theorem kern_e0_sub_zero {w : DressedFRD.Sym 2 (L ^ N)} (hw : w ∈ symSub) :
    DressedFRD.kern w (dirVec (Sum.inl 0) : Λ2) - DressedFRD.kern w 0 =
      -(1 / 2 : ℂ) * dop (Ai 0) (DressedFRD.kern w) 0 := by
  have hneg : DressedFRD.kern w (dirVec (Sum.inr 0) : Λ2) =
      DressedFRD.kern w (dirVec (Sum.inl 0)) := by
    rw [dirVec_inr_eq, kern_neg_of_symMem hw]
  rw [dop_eval]
  have e : ∀ y : Λ2, DressedFRD.kern w y = (((L ^ N : ℕ) : ℂ) ^ 2)⁻¹ * ∑ m, w m * char m y := by
    intro y; rfl
  have h2 : DressedFRD.kern w (dirVec (Sum.inl 0) : Λ2) +
      DressedFRD.kern w (dirVec (Sum.inr 0) : Λ2) - 2 * DressedFRD.kern w 0 =
      -((((L ^ N : ℕ) : ℂ) ^ 2)⁻¹ * ∑ m, w m * char m 0 * DressedFRD.sigma (Ai 0) m) := by
    rw [e, e, e]
    simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib, ← sum_neg_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [sigma_eval, char_inr, char_zero_right]
    have hA := char_ne_zero m (e0 (L := L) (N := N))
    simp [Ai]
    field_simp
    ring
  rw [hneg] at h2
  linear_combination h2 / 2

theorem norm_sigma_Ai_le_lam (m : Λ2) : ‖DressedFRD.sigma (Ai 0) m‖ ≤ lam m := by
  rw [lam_eq_sum_sigma, Fin.sum_univ_two]
  have h1 : ‖DressedFRD.sigma (Ai 0) m‖ = ‖DressedFRD.sigma (two 0) m‖ := by
    rw [sigma_eval, sigma_eval]
    simp only [Ai, two, Pi.add_apply, Pi.single_apply]
    simp
    have hA := char_ne_zero m (e0 (L := L) (N := N))
    have hn : ‖char m (e0 (L := L) (N := N))‖ = 1 := FRD.norm_char _ _
    have : ‖(char m (e0 (L := L) (N := N)))⁻¹ - 1‖ = ‖char m (e0 (L := L) (N := N)) - 1‖ := by
      rw [show (char m (e0 (L := L) (N := N)))⁻¹ - 1 =
        -(char m (e0 (L := L) (N := N)) - 1) / char m e0 by field_simp; ring]
      rw [norm_div, norm_neg, hn, div_one]
    rw [this, sq]
  rw [h1]
  have := norm_nonneg (DressedFRD.sigma (two 1) m)
  linarith

theorem wt_Ioc_le_Ioi {msq : ℝ} (hmsq : 0 < msq) {a b : ℝ} (ha : 0 ≤ a) (m : Λ2) :
    FRD.wt Pc msq (Set.Ioc a b) m ≤ FRD.wt Pc msq (Set.Ioi a) m := by
  unfold FRD.wt
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine setIntegral_mono_set (FRD.integrableOn_Ioi Pc (uhat_mem_Ioc hmsq m) ha)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => mul_nonneg (ha.trans ht.le)
      (Pc.nonneg t (lt_of_le_of_lt ha ht) _ (uhat_mem hmsq.le m)))
    (Filter.Eventually.of_forall fun t ht => ht.1)

theorem frdC_le_inv {msq : ℝ} (hmsq : 0 < msq) (hL : 1 ≤ L) (hN : 1 ≤ N) {k : ℕ}
    (hk1 : 1 ≤ k) (hkN : k ≤ N) (m : Λ2) :
    frdC Pc (d := 2) (n := L ^ N) msq L N k m ≤ (lam m + msq)⁻¹ := by
  rw [← frdC_sum Pc hmsq hL hN m]
  exact single_le_sum (f := fun k => frdC Pc (d := 2) (n := L ^ N) msq L N k m)
    (fun i _ => frdC_nonneg Pc hmsq.le i m) (mem_Icc.2 ⟨hk1, hkN⟩)

/-- **(S1), undressed**: `|C_{j+1}(e₀) - C_{j+1}(0)| ≤ M₂ L^{-2j}`, `M₂` independent of `L`. -/
theorem first_diff_le : ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ (L' N' : ℕ) [NeZero L'], 7 ≤ L' → ∀ msq : ℝ, 0 < msq →
    ∀ j : ℕ, j + 1 < N' →
      ‖DressedFRD.kern (ofR (frdC Pc (d := 2) (n := L' ^ N') msq L' N' (j + 1)))
          (dirVec (Sum.inl 0) : Lam 2 L' N') -
        DressedFRD.kern (ofR (frdC Pc (d := 2) (n := L' ^ N') msq L' N' (j + 1))) 0‖ ≤
        M₂ / ((L' : ℝ) ^ j) ^ 2 := by
  obtain ⟨Bt, hBt0, hBt⟩ := wt_Ioi_le Pc (d := 2) (by norm_num) (r := 2) (by norm_num)
  set B' : ℝ := 2 * Bt * 1024 + 16
  have hB'0 : 0 ≤ B' := by positivity
  have htail : 0 ≤ tailC 2 (4 : ℕ) := tailC_nonneg (by norm_num)
  refine ⟨(1 + B' * tailC 2 (4 : ℕ)) / 2, by positivity,
    fun L' N' _ hL msq hmsq j hjN => ?_⟩
  set C := frdC Pc (d := 2) (n := L' ^ N') msq L' N' (j + 1)
  have hL1 : 1 ≤ L' := by omega
  have hLr : (7 : ℝ) ≤ L' := by exact_mod_cast hL
  have hw : ofR C ∈ symSub := ofR_symMem (fun π s m => frdC_symm Pc msq L' N' (j + 1) π s m)
  rw [kern_e0_sub_zero hw, norm_mul, dop_eval]
  -- the average of `λ C`
  set R : ℝ := (L' : ℝ) ^ j
  have hR : 0 < R := by positivity
  have hR1 : 1 ≤ R := one_le_pow₀ (by linarith)
  have h7R : 7 * R ≤ ((L' ^ N' : ℕ) : ℝ) := by
    have h1 : (L' : ℝ) ^ (j + 1) ≤ (L' : ℝ) ^ N' := pow_le_pow_right₀ (by linarith) (by omega)
    have h2 : 7 * R ≤ (L' : ℝ) ^ (j + 1) := by simp only [R]; rw [pow_succ]; nlinarith
    push_cast; linarith
  have hC0 : ∀ m, 0 ≤ C m := fun m => frdC_nonneg Pc hmsq.le _ m
  have hlC1 : ∀ m : Lam 2 L' N', lam m * C m ≤ 1 := by
    intro m
    have hl := lam_nonneg m
    have h1 := frdC_le_inv (L := L') (N := N') hmsq hL1 (by omega) (k := j + 1) (by omega) (by omega) m
    have hp : 0 < lam m + msq := by linarith
    calc lam m * C m ≤ lam m * (lam m + msq)⁻¹ := mul_le_mul_of_nonneg_left h1 hl
      _ ≤ (lam m + msq) * (lam m + msq)⁻¹ := by gcongr; linarith
      _ = 1 := mul_inv_cancel₀ hp.ne'
  have hmain := avg_pnorm_pow_le (d := 2) (n := L' ^ N') (by norm_num)
    (w := fun m => lam m * C m) (B := 1) (B' := B') (R := R) 0 2 hR h7R (by norm_num)
    (fun m => mul_nonneg (lam_nonneg m) (hC0 m)) hlC1 hB'0 (fun m hm => by
      have hp0 : 0 < pnorm m := lt_of_le_of_lt (inv_nonneg.2 hR.le) hm
      have hpl : pnorm m ^ 2 ≤ lam m := pnorm_sq_le_lam (by norm_num) m
      have hl0 : 0 < lam m := lt_of_lt_of_le (by positivity) hpl
      rcases Nat.eq_zero_or_pos j with hj0 | hj1
      · -- `R = 1`
        have hR1' : R = 1 := by simp only [R, hj0, pow_zero]
        rw [hR1', one_mul]
        have hp2 := pnorm_le_two (d := 2) (n := L' ^ N') (by norm_num) m
        have : pnorm m ^ (2 * 2) ≤ 16 := by
          calc pnorm m ^ (2 * 2) ≤ 2 ^ (2 * 2) := pow_le_pow_left₀ (pnorm_nonneg m) hp2 _
            _ = 16 := by norm_num
        have h1 := hlC1 m
        have : lam m * C m * pnorm m ^ (2 * 2) ≤ 1 * 16 := by
          refine mul_le_mul h1 this (by positivity) (by norm_num)
        simp only [B']; nlinarith
      · -- `j ≥ 1`: decay beyond `T = L'^j/2`
        set T : ℝ := (L' : ℝ) ^ j / 2
        have hT : 0 ≤ T := by positivity
        have hCT : C m ≤ Bt * (((1 + lam m / (4 * 2) * T ^ 2) ^ 2)⁻¹ / (2 * (lam m / (4 * 2)) * 2)) := by
          have e : C m = FRD.wt Pc msq (Set.Ioc T ((L' : ℝ) ^ (j + 1) / 2)) m := by
            simp only [C]
            rw [frdC_of_lt Pc (by omega), FRD.lowEnd_succ _ hj1]
          rw [e]
          refine (wt_Ioc_le_Ioi hmsq hT m).trans ?_
          have := hBt (L' ^ N') msq hmsq T hT m hl0
          simpa using this
        set x := R ^ 2 * lam m
        have hx : 0 ≤ x := by positivity
        have hlT : lam m / (4 * 2) * T ^ 2 = x / 32 := by simp only [x, T, R]; ring
        rw [hlT] at hCT
        have hlC : lam m * C m ≤ 2 * Bt * ((1 + x / 32) ^ 2)⁻¹ := by
          calc lam m * C m ≤ lam m * (Bt * (((1 + x / 32) ^ 2)⁻¹ / (2 * (lam m / (4 * 2)) * 2))) :=
                mul_le_mul_of_nonneg_left hCT hl0.le
            _ = 2 * Bt * ((1 + x / 32) ^ 2)⁻¹ := by field_simp; ring
        have hRp : (R * pnorm m) ^ (2 * 2) ≤ x ^ 2 := by
          have : (R * pnorm m) ^ 2 ≤ x := by
            rw [mul_pow]; exact mul_le_mul_of_nonneg_left hpl (by positivity)
          calc (R * pnorm m) ^ (2 * 2) = ((R * pnorm m) ^ 2) ^ 2 := by ring
            _ ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) this 2
        have hq : x ^ 2 * ((1 + x / 32) ^ 2)⁻¹ ≤ 1024 := by
          rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; nlinarith
        calc lam m * C m * (R * pnorm m) ^ (2 * 2) ≤ 2 * Bt * ((1 + x / 32) ^ 2)⁻¹ * x ^ 2 :=
              mul_le_mul hlC hRp (by positivity) (by positivity)
          _ = 2 * Bt * (x ^ 2 * ((1 + x / 32) ^ 2)⁻¹) := by ring
          _ ≤ 2 * Bt * 1024 := by gcongr
          _ ≤ B' := by simp only [B']; linarith)
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add] at hmain
  -- from the Fourier sum to the average
  have hsum : ‖(((L' ^ N' : ℕ) : ℂ) ^ 2)⁻¹ * ∑ m : Lam 2 L' N', ofR C m * char m 0 * DressedFRD.sigma (Ai 0) m‖ ≤
      avg (fun m : Lam 2 L' N' => lam m * C m) := by
    rw [norm_mul]
    unfold avg
    have hn : ‖(((L' ^ N' : ℕ) : ℂ) ^ 2)⁻¹‖ = (((L' ^ N' : ℕ) : ℝ) ^ 2)⁻¹ := by simp
    rw [hn]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_))
      (by positivity)
    rw [char_zero_right, mul_one, norm_mul]
    simp only [ofR, Complex.norm_real, Real.norm_of_nonneg (hC0 m)]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_sigma_Ai_le_lam m) (hC0 m)
  have hRpow : R ^ (-((2 : ℕ) : ℝ)) = 1 / R ^ 2 := by
    rw [Real.rpow_neg hR.le, Real.rpow_natCast, one_div]
  rw [show ‖-(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  calc 1 / 2 * ‖(((L' ^ N' : ℕ) : ℂ) ^ 2)⁻¹ * ∑ m : Lam 2 L' N', ofR C m * char m 0 * DressedFRD.sigma (Ai 0) m‖
      ≤ 1 / 2 * avg (fun m : Lam 2 L' N' => lam m * C m) := by gcongr
    _ ≤ 1 / 2 * ((1 + B' * tailC 2 (4 : ℕ)) * R ^ (-((2 : ℕ) : ℝ))) := by
        gcongr
        convert hmain using 3
        norm_num
    _ = _ := by rw [hRpow]; field_simp

/-- **(S0), undressed**: `0 ≤ C_{≤j}(m) ≤ M₀ L'^{2j}`, `M₀` independent of `L'`. -/
theorem zmode_le : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ (L' N' : ℕ) [NeZero L'], 2 ≤ L' → ∀ msq : ℝ, 0 < msq →
    ∀ j : ℕ, j < N' → ∀ m : Lam 2 L' N',
      0 ≤ ∑ k ∈ Icc 1 j, frdC Pc (d := 2) (n := L' ^ N') msq L' N' k m ∧
      ∑ k ∈ Icc 1 j, frdC Pc (d := 2) (n := L' ^ N') msq L' N' k m ≤ M₀ * ((L' : ℝ) ^ j) ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := wt_Ioc_le Pc (d := 2) (by norm_num) 0
  refine ⟨B / 3, by positivity, fun L' N' _ hL msq hmsq j hjN m => ⟨?_, ?_⟩⟩
  · exact sum_nonneg fun k _ => frdC_nonneg Pc hmsq.le k m
  · have hL2 : (2 : ℝ) ≤ L' := by exact_mod_cast hL
    have hk : ∀ k ∈ Icc 1 j, frdC Pc (d := 2) (n := L' ^ N') msq L' N' k m ≤ B / 4 * (L' : ℝ) ^ (2 * k) := by
      intro k hk
      rw [frdC_of_lt Pc (by have := (mem_Icc.1 hk).2; omega)]
      have := hB (L' ^ N') msq hmsq.le (FRD.lowEnd L' k) ((L' : ℝ) ^ k / 2)
        (FRD.lowEnd_nonneg (by positivity) k) (FRD.lowEnd_le (by linarith) k) m
      simp only [pow_zero, inv_one, mul_one] at this
      refine this.trans (le_of_eq ?_)
      ring
    calc ∑ k ∈ Icc 1 j, frdC Pc (d := 2) (n := L' ^ N') msq L' N' k m
        ≤ ∑ k ∈ Icc 1 j, B / 4 * (L' : ℝ) ^ (2 * k) := sum_le_sum hk
      _ ≤ ∑ k ∈ range (j + 1), B / 4 * (L' : ℝ) ^ (2 * k) := by
          refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun _ _ _ => by positivity)
          simp only [mem_Icc] at hk; simp only [mem_range]; omega
      _ = B / 4 * ∑ k ∈ range (j + 1), (L' : ℝ) ^ (2 * k) := by rw [mul_sum]
      _ ≤ B / 4 * (4 / 3 * (L' : ℝ) ^ (2 * j)) := by gcongr; exact geom_sq_le hL2 j
      _ = B / 3 * ((L' : ℝ) ^ j) ^ 2 := by ring

end

end Step2