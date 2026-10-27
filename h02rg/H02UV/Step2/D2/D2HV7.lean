import Step2.D2.D2HV6

/-!
# The dressing of the bubble difference

With `A = w'_j`, `B = C'_{j+1}`, `A₀ = C_{≤j}`, `B₀ = C_{j+1}` (kernels truncated at `L^{j+1}`):

  `|(2𝔅x(A,B) + 𝔅x(B,B)) - (2𝔅x(A₀,B₀) + 𝔅x(B₀,B₀))| ≤ E₁ · M_z`

(`bub_dress`), `E₁ = 72(c_S+K)² + (112/3) c_S K + L²(8 + 2L² + 4L)(2c_S+K)K`.
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann DressedFRD DressedFRD.Data

variable {L N : ℕ} [NeZero L]

local notation "Λ2" => Lam 2 L N

/-- The polarisation identity for the dressing. -/
theorem bubX_dress_identity {a b a0 b0 : ℤ × ℤ → ℂ} (ha : Function.HasFiniteSupport a)
    (hb : Function.HasFiniteSupport b) (ha0 : Function.HasFiniteSupport a0)
    (hb0 : Function.HasFiniteSupport b0) :
    (2 * bubX a b + bubX b b) - (2 * bubX a0 b0 + bubX b0 b0) =
      2 * bubX (a - a0) b + 2 * bubX a0 (b - b0) + bubX (b - b0) (b + b0) := by
  have hbb : Function.HasFiniteSupport (b - b0) := by
    have := hfs_add hb (show Function.HasFiniteSupport (-b0) from
      Set.Finite.subset hb0 (fun v hv => by simpa using hv))
    simpa [sub_eq_add_neg] using this
  rw [bubX_sub_left ha ha0 hb, bubX_sub_left hb hb0 (hfs_add hb hb0),
    bubX_add_right hb hb hb0, bubX_add_right hb0 hb hb0, bubX_comm a0 (b - b0),
    bubX_sub_left hb hb0 ha0, bubX_comm b a0, bubX_comm b0 a0, bubX_comm b0 b]
  ring

/-- `S4a` as `dopB`. -/
theorem dopB_of_S4a {D : Data 2 (L ^ N)} {q M : ℕ} {cS : ℝ} (hS : StdFull L N q M D.msq cS D.C)
    (hq : 1 ≤ q) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) : dopB (ofR (D.C k)) cS ((L : ℝ) ^ (k - 1)) := by
  intro α hα x
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hM : 4 ≤ M := by have := hS.hM; omega
  refine (hS.S4a k hk1 hkN α (by omega) x).trans (le_of_eq ?_)
  rw [show ((2 : ℕ) : ℝ) - 2 + (Grassmann.mabs α : ℝ) = (Grassmann.mabs α : ℝ) by push_cast; ring,
    Real.rpow_neg hL0.le, ← Real.rpow_natCast ((L : ℝ) ^ (k - 1)),
    ← Real.rpow_natCast (L : ℝ) (k - 1), ← Real.rpow_mul hL0.le, div_eq_mul_inv]

/-- The bracket of `bubX_dop` at scale `ρ ≥ 1` with `R' ≤ ρ`. -/
theorem bracket_le {M ρ R' : ℝ} (hM : 0 ≤ M) (hρ : 1 ≤ ρ) (hR0 : 0 ≤ R') (hR : R' ≤ ρ) :
    4 * (M / ρ ^ 2) + 4 * M / ρ ^ 4 + R' * (R' * (4 * M / ρ ^ 4) + 2 * (4 * M / ρ ^ 3)) / 2 ≤
      14 * M / ρ ^ 2 := by
  have hρ0 : 0 < ρ := by linarith
  have h1 : 4 * M / ρ ^ 4 ≤ 4 * M / ρ ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hρ (by norm_num))
  have h2 : R' * (R' * (4 * M / ρ ^ 4)) ≤ ρ * (ρ * (4 * M / ρ ^ 4)) := by gcongr
  have h3 : R' * (2 * (4 * M / ρ ^ 3)) ≤ ρ * (2 * (4 * M / ρ ^ 3)) := by gcongr
  have e2 : ρ * (ρ * (4 * M / ρ ^ 4)) = 4 * M / ρ ^ 2 := by field_simp
  have e3 : ρ * (2 * (4 * M / ρ ^ 3)) = 8 * M / ρ ^ 2 := by field_simp; ring
  have : R' * (R' * (4 * M / ρ ^ 4) + 2 * (4 * M / ρ ^ 3)) / 2 ≤ 6 * M / ρ ^ 2 := by
    rw [mul_add]
    have : (4 * M / ρ ^ 2 + 8 * M / ρ ^ 2) / 2 = 6 * M / ρ ^ 2 := by ring
    linarith
  have e4 : 4 * (M / ρ ^ 2) = 4 * M / ρ ^ 2 := by ring
  calc _ ≤ 4 * M / ρ ^ 2 + 4 * M / ρ ^ 2 + 6 * M / ρ ^ 2 := by rw [e4]; linarith
    _ = 14 * M / ρ ^ 2 := by ring

section Dress

variable (D : Data 2 (L ^ N)) {q M : ℕ} {cS K : ℝ}

/-- **The dressing of the bubble difference.** -/
theorem bub_dress (hS : StdFull L N q M D.msq cS D.C) (hq : 4 ≤ q) (hL : 2 ≤ L)
    (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 8) (hK : 0 ≤ K)
    (hclose : ∀ i, i + 1 < N →
      snorm (L : ℝ) q i (D.Z (i + 1) • D.Gint i - ofR (D.C (i + 1))) ≤ K * D.Mz (i + 1))
    (hrange : ∀ i, i + 1 < N → 2 * rng (D.Gint i) < L ^ (i + 1))
    {j : ℕ} (hjN : j + 1 < N) (hn : 2 * (L ^ (j + 1) + 4) < L ^ N) :
    ‖(2 * bubX (cKer (L ^ (j + 1)) (wp D j)) (cKer (L ^ (j + 1)) (Cp D (j + 1))) +
          bubX (cKer (L ^ (j + 1)) (Cp D (j + 1))) (cKer (L ^ (j + 1)) (Cp D (j + 1)))) -
        (2 * bubX (cKer (L ^ (j + 1)) (Cle D.C j)) (cKer (L ^ (j + 1)) (ofR (D.C (j + 1)))) +
          bubX (cKer (L ^ (j + 1)) (ofR (D.C (j + 1)))) (cKer (L ^ (j + 1)) (ofR (D.C (j + 1)))))‖ ≤
      (72 * (cS + K) ^ 2 + 112 / 3 * cS * K +
        (L : ℝ) ^ 2 * (8 + 2 * (L : ℝ) ^ 2 + 4 * L) * (2 * cS + K) * K) * D.Mz (j + 1) := by
  set R := L ^ (j + 1)
  set Lr : ℝ := (L : ℝ)
  have hL0 : 0 < Lr := by simp only [Lr]; exact_mod_cast (by omega : 0 < L)
  have hL2 : (2 : ℝ) ≤ Lr := by simp only [Lr]; exact_mod_cast hL
  have hL1 : 1 ≤ L := by omega
  have hζ2 : ∀ i, ‖D.ζ i‖ ≤ 1 / 2 := fun i => (hζ i).trans (by norm_num)
  set Mz := D.Mz (j + 1)
  have hMz0 : 0 ≤ Mz := Mz_nonneg _
  have hMz : Mz ≤ 1 / 8 := Mz_le (by norm_num) fun i _ => hζ i
  have hcS := hS.hcS
  set δ : ℕ → Sym 2 (L ^ N) := fun k => Cp D k - ofR (D.C k)
  have hδsn : ∀ k, 1 ≤ k → k < N → snorm Lr q (k - 1) (δ k) ≤ K * D.Mz k := by
    intro k hk1 hkN
    have := hclose (k - 1) (by omega)
    rwa [show k - 1 + 1 = k by omega] at this
  have hrngC : ∀ k, 1 ≤ k → k < N → 2 * rng (ofR (D.C k)) < L ^ k := fun k hk1 hkN =>
    hS.base.range k hk1 hkN
  have hrngδ : ∀ k, 1 ≤ k → k < N → 2 * rng (δ k) < L ^ k := by
    intro k hk1 hkN
    have h1 := hrange (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at h1
    have h2 := hrngC k hk1 hkN
    have h3 : rng (δ k) ≤ max (rng (Cp D k)) (rng (ofR (D.C k))) := rng_sub_le _ _
    have h4 : rng (Cp D k) ≤ rng (D.Gint (k - 1)) := rng_smul_le _ _
    omega
  have hkδ : ∀ k, 1 ≤ k → k < N → k ≤ j + 1 → ∀ x, ‖kern (δ k) x‖ ≤ K * Mz := by
    intro k hk1 hkN hkj x
    refine (norm_kern_le_snorm hL0 q (k - 1) _ x).trans ((hδsn k hk1 hkN).trans ?_)
    gcongr; exact Mz_mono (by omega)
  have hkC : ∀ k, 1 ≤ k → k < N → ∀ x, ‖kern (ofR (D.C k)) x‖ ≤ cS := fun k hk1 hkN x =>
    (norm_kern_le_snorm hL0 q (k - 1) _ x).trans (std_c hS hL1 hk1 hkN)
  have hsumδ : ∀ k, 1 ≤ k → k < N → k ≤ j + 1 →
      ∑ x : Λ2, ‖kern (δ k) x‖ ≤ (Lr ^ k) ^ 2 * (K * Mz) := fun k hk1 hkN hkj =>
    kern_sum_le (hrngδ k hk1 hkN) (hkδ k hk1 hkN hkj)
  have hsumC : ∀ k, 1 ≤ k → k < N → ∑ x : Λ2, ‖kern (ofR (D.C k)) x‖ ≤ (Lr ^ k) ^ 2 * cS :=
    fun k hk1 hkN => kern_sum_le (hrngC k hk1 hkN) (hkC k hk1 hkN)
  -- derivative bounds at scale `L^j`
  have hρ : (1 : ℝ) ≤ Lr ^ j := one_le_pow₀ (by linarith)
  have hρ0 : 0 < Lr ^ j := by positivity
  have hdδ : dopB (δ (j + 1)) (K * Mz) (Lr ^ j) := by
    have := dopB_of_snorm (L := L) (N := N) hq (hδsn (j + 1) (by omega) hjN)
    simpa using this
  have hdC : dopB (ofR (D.C (j + 1))) cS (Lr ^ j) := by
    have := dopB_of_S4a hS (by omega) (k := j + 1) (by omega) hjN
    simpa using this
  have hCpe : Cp D (j + 1) = ofR (D.C (j + 1)) + δ (j + 1) := by simp [δ]
  have hdB : dopB (Cp D (j + 1)) (cS + K * Mz) (Lr ^ j) := by
    rw [hCpe]; exact dopB_add hdC hdδ
  have hdBB : dopB (Cp D (j + 1) + ofR (D.C (j + 1))) (2 * cS + K * Mz) (Lr ^ j) := by
    rw [hCpe]
    have := dopB_add (dopB_add hdC hdδ) hdC
    refine dopB_mono (by simpa [add_comm, add_left_comm, add_assoc] using this) (by linarith) hρ0
  -- ranges
  have hRj : ∀ k, k ≤ j + 1 → L ^ k ≤ R := fun k hk => Nat.pow_le_pow_right (by omega) hk
  have hrCp : rng (Cp D (j + 1)) ≤ R := by
    have := hrange j hjN; have := rng_smul_le (D.Z (j + 1)) (D.Gint j)
    simp only [Cp, show j + 1 - 1 = j by omega]; omega
  have hrC1 : rng (ofR (D.C (j + 1))) ≤ R := by have := hrngC (j + 1) (by omega) hjN; omega
  have hrδ1 : rng (δ (j + 1)) ≤ R := by have := hrngδ (j + 1) (by omega) hjN; omega
  have hn' : 2 * (R + 4) < L ^ N := hn
  -- the identity
  have hid := bubX_dress_identity (cKer_hfs R (wp D j)) (cKer_hfs R (Cp D (j + 1)))
    (cKer_hfs R (Cle D.C j)) (cKer_hfs R (ofR (D.C (j + 1))))
  rw [hid, ← cKer_sub, ← cKer_sub, ← cKer_add]
  have hδ1 : Cp D (j + 1) - ofR (D.C (j + 1)) = δ (j + 1) := rfl
  rw [hδ1]
  -- T1
  set ρ : ℕ → ℂ := fun k => D.Z (j + 1) / D.Z k
  have hdec : wp D j - Cle D.C j =
      ∑ k ∈ Icc 1 j, (ρ k • δ k + (ρ k - 1) • ofR (D.C k)) := by
    simp only [wp, Cle, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [δ, ρ, smul_sub, sub_smul, one_smul]; abel
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
  have hT1 : ‖bubX (cKer R (wp D j - Cle D.C j)) (cKer R (Cp D (j + 1)))‖ ≤
      36 * (cS + K) ^ 2 * Mz := by
    rw [hdec, cKer_sum, bubX_sum_left _ (fun k => cKer_hfs R _) (cKer_hfs R _)]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k ∈ Icc 1 j, ‖bubX (cKer R (ρ k • δ k + (ρ k - 1) • ofR (D.C k)))
        (cKer R (Cp D (j + 1)))‖ ≤ 9 / 8 * (9 / 16) ^ (j - k) * (14 * (cS + K) * ((K + cS) * Mz)) := by
      intro k hk
      have hk' := mem_Icc.1 hk
      have hkN : k < N := by omega
      obtain ⟨r1, r2⟩ := hρb k hk
      obtain ⟨c1, c2⟩ := coef_bound hL2 hMz0 hMz hk'.2
      have hra : rng (ρ k • δ k + (ρ k - 1) • ofR (D.C k)) ≤ L ^ k := by
        have h1 := rng_add_le (ρ k • δ k) ((ρ k - 1) • ofR (D.C k))
        have h2 := rng_smul_le (ρ k) (δ k)
        have h3 := rng_smul_le (ρ k - 1) (ofR (D.C k))
        have h4 := hrngδ k hk'.1 hkN
        have h5 := hrngC k hk'.1 hkN
        omega
      have hb := bubX_dop hn' hrCp hra (hRj k (by omega)) hρ0 hdB
      have hbr := bracket_le (M := cS + K * Mz) (ρ := Lr ^ j) (R' := ((L ^ k : ℕ) : ℝ))
        (by positivity) hρ (by positivity)
        (by push_cast; exact pow_le_pow_right₀ (by linarith) hk'.2)
      have hsum : ∑ x : Λ2, ‖kern (ρ k • δ k + (ρ k - 1) • ofR (D.C k)) x‖ ≤
          (Lr ^ k) ^ 2 * (‖ρ k‖ * (K * Mz) + ‖ρ k - 1‖ * cS) := by
        calc ∑ x : Λ2, ‖kern (ρ k • δ k + (ρ k - 1) • ofR (D.C k)) x‖
            ≤ ∑ x : Λ2, (‖ρ k‖ * ‖kern (δ k) x‖ + ‖ρ k - 1‖ * ‖kern (ofR (D.C k)) x‖) := by
              refine sum_le_sum fun x _ => ?_
              rw [kern_add, kern_smul, kern_smul]
              refine (norm_add_le _ _).trans ?_
              rw [norm_mul, norm_mul]
          _ = ‖ρ k‖ * ∑ x : Λ2, ‖kern (δ k) x‖ + ‖ρ k - 1‖ * ∑ x : Λ2, ‖kern (ofR (D.C k)) x‖ := by
              rw [sum_add_distrib, mul_sum, mul_sum]
          _ ≤ ‖ρ k‖ * ((Lr ^ k) ^ 2 * (K * Mz)) + ‖ρ k - 1‖ * ((Lr ^ k) ^ 2 * cS) := by
              gcongr
              · exact hsumδ k hk'.1 hkN (by omega)
              · exact hsumC k hk'.1 hkN
          _ = _ := by ring
      have hKM : K * Mz ≤ K := by nlinarith
      have hM1 : cS + K * Mz ≤ cS + K := by linarith
      calc _ ≤ (∑ x : Λ2, ‖kern (ρ k • δ k + (ρ k - 1) • ofR (D.C k)) x‖) *
            (14 * (cS + K * Mz) / (Lr ^ j) ^ 2) :=
            hb.trans (mul_le_mul_of_nonneg_left (by push_cast at hbr ⊢; exact hbr)
              (sum_nonneg fun _ _ => norm_nonneg _))
        _ ≤ (Lr ^ k) ^ 2 * (‖ρ k‖ * (K * Mz) + ‖ρ k - 1‖ * cS) * (14 * (cS + K) / (Lr ^ j) ^ 2) := by
            gcongr
        _ = 14 * (cS + K) * (‖ρ k‖ * ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹) * (K * Mz) +
              ‖ρ k - 1‖ * ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹) * cS) := by
            field_simp
        _ ≤ 14 * (cS + K) * (9 / 8 * (9 / 16) ^ (j - k) * (K * Mz) +
              9 / 8 * (9 / 16) ^ (j - k) * Mz * cS) := by
            have hq : 0 ≤ (Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹ := by positivity
            have e1 : ‖ρ k‖ * ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹) ≤ 9 / 8 * (9 / 16) ^ (j - k) :=
              (mul_le_mul_of_nonneg_right r1 hq).trans c2
            have e2 : ‖ρ k - 1‖ * ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹) ≤
                9 / 8 * (9 / 16) ^ (j - k) * Mz := by
              refine (mul_le_mul_of_nonneg_right r2 hq).trans ?_
              calc ((j + 1 - k : ℕ) : ℝ) * Mz * (1 + Mz) ^ (j + 1 - k) *
                    ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹) =
                    Mz * (((j + 1 - k : ℕ) : ℝ) * (1 + Mz) ^ (j + 1 - k) *
                      ((Lr ^ k) ^ 2 * ((Lr ^ j) ^ 2)⁻¹)) := by ring
                _ ≤ Mz * (9 / 8 * (9 / 16) ^ (j - k)) := mul_le_mul_of_nonneg_left c1 hMz0
                _ = _ := by ring
            gcongr
        _ = 9 / 8 * (9 / 16) ^ (j - k) * (14 * (cS + K) * ((K + cS) * Mz)) := by ring
    refine (sum_le_sum hterm).trans ?_
    rw [← sum_mul]
    have hg := geom_Icc_le j
    have hp : 0 ≤ 14 * (cS + K) * ((K + cS) * Mz) := by positivity
    calc (∑ i ∈ Icc 1 j, (9 / 8 : ℝ) * (9 / 16) ^ (j - i)) * (14 * (cS + K) * ((K + cS) * Mz))
        = 9 / 8 * (∑ i ∈ Icc 1 j, ((9 : ℝ) / 16) ^ (j - i)) * (14 * (cS + K) * ((K + cS) * Mz)) := by
          rw [mul_sum]
      _ ≤ 9 / 8 * (16 / 7) * (14 * (cS + K) * ((K + cS) * Mz)) := by gcongr
      _ = 36 * (cS + K) ^ 2 * Mz := by ring
  -- T2
  have hT2 : ‖bubX (cKer R (Cle D.C j)) (cKer R (δ (j + 1)))‖ ≤ 56 / 3 * cS * K * Mz := by
    have hrCle : rng (Cle D.C j) ≤ L ^ j := by
      unfold Cle
      refine rng_sum_le _ _ fun k hk => ?_
      have := hrngC k (mem_Icc.1 hk).1 (by have := (mem_Icc.1 hk).2; omega)
      have : L ^ k ≤ L ^ j := Nat.pow_le_pow_right (by omega) (mem_Icc.1 hk).2
      omega
    have hb := bubX_dop hn' hrδ1 hrCle (hRj j (by omega)) hρ0 hdδ
    have hbr := bracket_le (M := K * Mz) (ρ := Lr ^ j) (R' := ((L ^ j : ℕ) : ℝ))
      (by positivity) hρ (by positivity) (by push_cast; exact le_rfl)
    have hsum : ∑ x : Λ2, ‖kern (Cle D.C j) x‖ ≤ 4 / 3 * (Lr ^ j) ^ 2 * cS := by
      calc ∑ x : Λ2, ‖kern (Cle D.C j) x‖ ≤ ∑ x : Λ2, ∑ k ∈ Icc 1 j, ‖kern (ofR (D.C k)) x‖ :=
            sum_le_sum fun x _ => by unfold Cle; rw [kern_sum]; exact norm_sum_le _ _
        _ = ∑ k ∈ Icc 1 j, ∑ x : Λ2, ‖kern (ofR (D.C k)) x‖ := sum_comm
        _ ≤ ∑ k ∈ Icc 1 j, (Lr ^ k) ^ 2 * cS := sum_le_sum fun k hk =>
            hsumC k (mem_Icc.1 hk).1 (by have := (mem_Icc.1 hk).2; omega)
        _ ≤ ∑ k ∈ range (j + 1), (Lr ^ k) ^ 2 * cS := by
            refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun _ _ _ => by positivity)
            simp only [mem_Icc] at hk; simp only [mem_range]; omega
        _ = (∑ k ∈ range (j + 1), Lr ^ (2 * k)) * cS := by
            rw [sum_mul]; exact sum_congr rfl fun k _ => by ring
        _ ≤ (4 / 3 * Lr ^ (2 * j)) * cS := by gcongr; exact geom_sq_le hL2 j
        _ = 4 / 3 * (Lr ^ j) ^ 2 * cS := by ring
    calc _ ≤ (∑ x : Λ2, ‖kern (Cle D.C j) x‖) * (14 * (K * Mz) / (Lr ^ j) ^ 2) :=
          hb.trans (mul_le_mul_of_nonneg_left (by push_cast at hbr ⊢; exact hbr)
            (sum_nonneg fun _ _ => norm_nonneg _))
      _ ≤ (4 / 3 * (Lr ^ j) ^ 2 * cS) * (14 * (K * Mz) / (Lr ^ j) ^ 2) := by gcongr
      _ = 56 / 3 * cS * K * Mz := by field_simp; ring
  -- T3
  have hT3 : ‖bubX (cKer R (δ (j + 1))) (cKer R (Cp D (j + 1) + ofR (D.C (j + 1))))‖ ≤
      Lr ^ 2 * (8 + 2 * Lr ^ 2 + 4 * Lr) * (2 * cS + K) * K * Mz := by
    have hrc : rng (Cp D (j + 1) + ofR (D.C (j + 1))) ≤ R :=
      (rng_add_le _ _).trans (max_le hrCp hrC1)
    have hb := bubX_dop hn' hrc hrδ1 le_rfl hρ0 hdBB
    have hsum := hsumδ (j + 1) (by omega) hjN le_rfl
    have hM0 : 0 ≤ 2 * cS + K * Mz := by positivity
    have hKM : K * Mz ≤ K := by nlinarith
    have hR : ((R : ℕ) : ℝ) = Lr * Lr ^ j := by simp only [R, Lr]; push_cast; ring
    have hbr : 4 * ((2 * cS + K * Mz) / (Lr ^ j) ^ 2) + 4 * (2 * cS + K * Mz) / (Lr ^ j) ^ 4 +
        (R : ℝ) * ((R : ℝ) * (4 * (2 * cS + K * Mz) / (Lr ^ j) ^ 4) +
          2 * (4 * (2 * cS + K * Mz) / (Lr ^ j) ^ 3)) / 2 ≤
        (2 * cS + K) * (8 + 2 * Lr ^ 2 + 4 * Lr) / (Lr ^ j) ^ 2 := by
      rw [hR]
      have hρ4 : 1 / (Lr ^ j) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have e : 4 * ((2 * cS + K * Mz) / (Lr ^ j) ^ 2) + 4 * (2 * cS + K * Mz) / (Lr ^ j) ^ 4 +
          Lr * Lr ^ j * (Lr * Lr ^ j * (4 * (2 * cS + K * Mz) / (Lr ^ j) ^ 4) +
            2 * (4 * (2 * cS + K * Mz) / (Lr ^ j) ^ 3)) / 2 =
          (2 * cS + K * Mz) * (4 + 4 * (1 / (Lr ^ j) ^ 2) + 2 * Lr ^ 2 + 4 * Lr) / (Lr ^ j) ^ 2 := by
        field_simp; ring
      rw [e]
      have h1 : (2 * cS + K * Mz) * (4 + 4 * (1 / (Lr ^ j) ^ 2) + 2 * Lr ^ 2 + 4 * Lr) ≤
          (2 * cS + K) * (8 + 2 * Lr ^ 2 + 4 * Lr) := by
        have : 4 + 4 * (1 / (Lr ^ j) ^ 2) + 2 * Lr ^ 2 + 4 * Lr ≤ 8 + 2 * Lr ^ 2 + 4 * Lr := by
          linarith
        have h0 : 0 ≤ 4 + 4 * (1 / (Lr ^ j) ^ 2) + 2 * Lr ^ 2 + 4 * Lr := by positivity
        calc _ ≤ (2 * cS + K) * (4 + 4 * (1 / (Lr ^ j) ^ 2) + 2 * Lr ^ 2 + 4 * Lr) := by gcongr
          _ ≤ _ := by gcongr
      exact div_le_div_of_nonneg_right h1 (by positivity)
    calc _ ≤ (∑ x : Λ2, ‖kern (δ (j + 1)) x‖) *
          ((2 * cS + K) * (8 + 2 * Lr ^ 2 + 4 * Lr) / (Lr ^ j) ^ 2) :=
          hb.trans (mul_le_mul_of_nonneg_left hbr (sum_nonneg fun _ _ => norm_nonneg _))
      _ ≤ ((Lr ^ (j + 1)) ^ 2 * (K * Mz)) *
          ((2 * cS + K) * (8 + 2 * Lr ^ 2 + 4 * Lr) / (Lr ^ j) ^ 2) := by
          gcongr
      _ = Lr ^ 2 * (8 + 2 * Lr ^ 2 + 4 * Lr) * (2 * cS + K) * K * Mz := by
          field_simp; ring
  calc _ ≤ ‖2 * bubX (cKer R (wp D j - Cle D.C j)) (cKer R (Cp D (j + 1)))‖ +
        ‖2 * bubX (cKer R (Cle D.C j)) (cKer R (δ (j + 1)))‖ +
        ‖bubX (cKer R (δ (j + 1))) (cKer R (Cp D (j + 1) + ofR (D.C (j + 1))))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2 * (36 * (cS + K) ^ 2 * Mz) + 2 * (56 / 3 * cS * K * Mz) +
        Lr ^ 2 * (8 + 2 * Lr ^ 2 + 4 * Lr) * (2 * cS + K) * K * Mz := by
        rw [norm_mul, norm_mul, Complex.norm_ofNat]
        gcongr
    _ = _ := by ring

end Dress

end

end Step2