import Step2.D2.D2HV12

/-!
# (HD): bounds on `q̃` and the weighted past coefficients

**(HD)** `|q̃| ≤ K_B` and `∑_{k<j} (j-k+1) 2^{j-k} |b̃_k| ≤ K_B`, `K_B` depending on `L` only.

Ingredients: `b_{j,k} = 2𝔅x(C_k, C_j) + T_{j,k}` (`beta_past_bubX`), `T_{j,k} = 16 δ_j Ĉ_k(0)`
(`tadT_eq`), the bilinear bound (`bubX_dop`), and the geometric decay `L^{-2(j-k)}`.
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann DressedFRD DressedFRD.Data

variable {L N : ℕ} [NeZero L]

local notation "Λ2" => Lam 2 L N

theorem geom_half_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    ∀ j : ℕ, ∑ k ∈ range j, x ^ (j - k) ≤ 1
  | 0 => by simp
  | j + 1 => by
    have ih := geom_half_le hx0 hx j
    have e : ∑ k ∈ range (j + 1), x ^ (j + 1 - k) = x * (∑ k ∈ range j, x ^ (j - k) + 1) := by
      rw [sum_range_succ, mul_add, mul_sum, mul_one, show j + 1 - j = 1 by omega, pow_one]
      congr 1
      · refine sum_congr rfl fun k hk => ?_
        rw [show j + 1 - k = (j - k) + 1 by have := mem_range.1 hk; omega, pow_succ]; ring
    rw [e]
    have : 0 ≤ ∑ k ∈ range j, x ^ (j - k) := sum_nonneg fun _ _ => by positivity
    nlinarith

theorem succ_le_two_pow (t : ℕ) : ((t + 1 : ℕ) : ℝ) ≤ 2 ^ t := by
  have : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
  exact_mod_cast this

set_option maxHeartbeats 1000000 in
/-- **The individual normalised past coefficient.** -/
theorem bTil_eq (D : Data 2 (L ^ N)) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {j k : ℕ} (hkj : k < j)
    (hjN : j + 1 < N) (hC : ∀ k π s m, D.C k (symmDual π s m) = D.C k m)
    (hrng : ∀ k ≤ j, 2 * DressedFRD.rng (D.Gint k) < L ^ (k + 1)) (hZ : ∀ i, D.Z i ≠ 0)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hG : ∀ i ≤ j, GoodCov2 i ℓ (DressedFRD.kmat (D.Gint i)))
    (κ : ℕ → Coup) :
    bTil D κ j k = (D.Z (j + 1) / D.Z (k + 1)) *
      (2 * bubX (cKer (L ^ (j + 1)) (Cp D (k + 1))) (cKer (L ^ (j + 1)) (Cp D (j + 1))) +
        16 * (DressedFRD.kern (Cp D (j + 1)) (dirVec (Sum.inl 0)) -
          DressedFRD.kern (Cp D (j + 1)) 0) * Cp D (k + 1) 0) := by
  set R := L ^ (j + 1)
  set z := D.Z (j + 1)
  set FS : FlowSeq 2 L N := ⟨fun k => DressedFRD.kmat (D.Gint k), fun _ => 1, κ⟩
  set FT : FlowSeq 2 L N :=
    ⟨fun k => if k ≤ j then DressedFRD.kmat (D.Gint k) else 0, fun _ => 1, κ⟩
  have hsym : ∀ k, D.Gint k ∈ symSub := fun k => DData.Gint_symMem hC k
  have hR : ∀ k ≤ j, DressedFRD.rng (D.Gint k) ≤ R := fun k hk => rng_le_of_two_lt hk (hrng k hk)
  have hb : (0 : Fin 2 → ℕ) ∈ blockIdx (L := L) (N := N) j := zero_mem_blockIdx j
  have hne : (Bp (L := L) (N := N) j (0 : Fin 2 → ℕ)).Nonempty :=
    (isSmall_clo (isSmall_blockSet_of_mem hb)).2.1.1
  have hreg := region_of_size (d := 2) (by norm_num) hL hjN hb
  have hX3 : ∀ x ∈ Bp (L := L) (N := N) j (0 : Fin 2 → ℕ),
      2 * (supNorm (x - base (Bp (L := L) (N := N) j (0 : Fin 2 → ℕ))) + R + 3) < L ^ N :=
      fun x hx => by have := hreg x hx; omega
  have hn : 2 * (R + 4) < L ^ N := by
    obtain ⟨x, hx⟩ := hne; have := hreg x hx; omega
  have hFTC : ∀ i, FT.C i = if i ≤ j then DressedFRD.kmat (D.Gint i) else 0 := fun i => rfl
  have hFSC : ∀ i, FS.C i = DressedFRD.kmat (D.Gint i) := fun i => rfl
  have hFTgood : ∀ i, GoodCov2 i ℓ (FT.C i) := fun i => by
    by_cases hi : i ≤ j
    · rw [hFTC, if_pos hi]; exact hG i hi
    · rw [hFTC, if_neg hi]; exact goodCov2_zero i hℓ
  have hbeta : FS.beta j k 0 0 = FT.beta j k 0 0 :=
    FlowSeq.beta_congr (D := FS) (D' := FT) (j := j) (k := k) hkj.le
      (fun i _ hi => by rw [hFTC, if_pos hi, hFSC]) (fun _ _ _ => rfl) 0 0
  have hCk : ∀ x y, FT.C k x y = cTor (cKer R (D.Gint k)) (x - y) := fun x y => by
    rw [hFTC, if_pos hkj.le]; exact kmat_eq_cTor (hR k hkj.le) x y
  have hCj : ∀ x y, FT.C j x y = cTor (cKer R (D.Gint j)) (x - y) := fun x y => by
    rw [hFTC, if_pos le_rfl]; exact kmat_eq_cTor (hR j le_rfl) x y
  have hb1 := FT.beta_past_bubX hL (fun _ => rfl) hkj hjN hFTgood hb
    (fun u hu => cKer_range _ hu) (fun u hu => cKer_range _ hu)
    (cKer_even (hsym k)) (cKer_even (hsym j)) hCk hCj hn hX3
  have hT := tadT_eq (d := 2) hL (by omega : j < N) hb 0 (w := FT.C k) (C := FT.C j)
    (by rw [hFTC, if_pos hkj.le]; exact kmat_CovH (hsym k) (hR k hkj.le) (by omega))
    (fun x hx => hreg x hx)
    (c₀ := DressedFRD.kern (D.Gint j) 0)
    (δ := DressedFRD.kern (D.Gint j) (dirVec (Sum.inl 0)) - DressedFRD.kern (D.Gint j) 0)
    (fun x => by rw [hFTC, if_pos le_rfl]; simp [DressedFRD.kmat])
    (fun x e => by
      rw [hFTC, if_pos le_rfl]
      simp only [DressedFRD.kmat, add_sub_cancel_left]
      rw [kern_dirVec_eq (hsym j)]; ring)
    (fun x e => by
      rw [hFTC, if_pos le_rfl]
      simp only [DressedFRD.kmat, sub_add_cancel_left]
      rw [kern_neg_of_symMem (hsym j), kern_dirVec_eq (hsym j)]; ring)
  have hbeta' : FS.beta j k 0 0 (eC 3) (eC 3) 3 = FT.beta j k 0 0 (eC 3) (eC 3) 3 := by
    rw [hbeta]
  rw [hb1, hT] at hbeta'
  have hsumk : ∑ x : Λ2, FT.C k x 0 = D.Gint k 0 := by
    rw [hFTC, if_pos hkj.le]
    simp only [DressedFRD.kmat, sub_zero]; exact sum_kern_eq _
  rw [hsumk] at hbeta'
  -- normalise
  have hCpk : Cp D (k + 1) = D.Z (k + 1) • D.Gint k := by simp [Cp]
  have hCpj : Cp D (j + 1) = z • D.Gint j := by simp [Cp, z]
  unfold bTil
  rw [show (gFS D κ) = FS from rfl, hbeta', hCpk, hCpj, cKer_smul, cKer_smul, bubX_smul_left,
    bubX_smul_right, DressedFRD.kern_smul, DressedFRD.kern_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hzk := hZ (k + 1)
  field_simp
  push_cast
  ring

/-- `q̃ = 𝔅x(C'_{j+1}, C'_{j+1})`. -/
theorem qTil_eq (D : Data 2 (L ^ N)) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {j : ℕ} (hjN : j + 1 < N)
    (hC : ∀ k π s m, D.C k (symmDual π s m) = D.C k m)
    (hrng : 2 * DressedFRD.rng (D.Gint j) < L ^ (j + 1)) (κ : ℕ → Coup) :
    qTil D κ j = bubX (cKer (L ^ (j + 1)) (Cp D (j + 1))) (cKer (L ^ (j + 1)) (Cp D (j + 1))) := by
  set R := L ^ (j + 1)
  have hsym : D.Gint j ∈ symSub := DData.Gint_symMem hC j
  have hR : DressedFRD.rng (D.Gint j) ≤ R := rng_le_of_two_lt le_rfl hrng
  have hb : (0 : Fin 2 → ℕ) ∈ blockIdx (L := L) (N := N) j := zero_mem_blockIdx j
  have hne : (Bp (L := L) (N := N) j (0 : Fin 2 → ℕ)).Nonempty :=
    (isSmall_clo (isSmall_blockSet_of_mem hb)).2.1.1
  have hreg := region_of_size (d := 2) (by norm_num) hL hjN hb
  have hX3 : ∀ x ∈ Bp (L := L) (N := N) j (0 : Fin 2 → ℕ),
      2 * (supNorm (x - base (Bp (L := L) (N := N) j (0 : Fin 2 → ℕ))) + R + 3) < L ^ N :=
      fun x hx => by have := hreg x hx; omega
  have hn : 2 * (R + 4) < L ^ N := by
    obtain ⟨x, hx⟩ := hne; have := hreg x hx; omega
  have h1 := (gFS D κ).betaQ_eq_negBub hL (by omega) hb 0
  have h2 : (gFS D κ).C j = DressedFRD.kmat (D.Gint j) := rfl
  rw [h2, negBub_kmat hsym hR hn hne hX3] at h1
  unfold qTil
  rw [h1]
  have hCpj : Cp D (j + 1) = D.Z (j + 1) • D.Gint j := by simp [Cp]
  rw [hCpj, cKer_smul, bubX_smul_left, bubX_smul_right]
  ring

theorem bracket_le2 {M ρ Lr : ℝ} (hM : 0 ≤ M) (hρ : 1 ≤ ρ) (hL0 : 0 ≤ Lr) :
    4 * (M / ρ ^ 2) + 4 * M / ρ ^ 4 + Lr * ρ * (Lr * ρ * (4 * M / ρ ^ 4) + 2 * (4 * M / ρ ^ 3)) / 2
      ≤ M * (8 + 2 * Lr ^ 2 + 4 * Lr) / ρ ^ 2 := by
  have hρ0 : 0 < ρ := by linarith
  have e : 4 * (M / ρ ^ 2) + 4 * M / ρ ^ 4 + Lr * ρ * (Lr * ρ * (4 * M / ρ ^ 4) + 2 * (4 * M / ρ ^ 3)) / 2
      = M * (4 + 4 * (1 / ρ ^ 2) + 2 * Lr ^ 2 + 4 * Lr) / ρ ^ 2 := by field_simp; ring
  rw [e]
  have h1 : 1 / ρ ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ hM
  linarith

/-- The per-scale facts for `C'_k = Z_k Γ^int_{k-1}`. -/
theorem Cp_facts (D : Data 2 (L ^ N)) {q M : ℕ} {cS K : ℝ} (hS : StdFull L N q M D.msq cS D.C)
    (hq : 4 ≤ q)
    (hclose : ∀ i, i + 1 < N →
      snorm (L : ℝ) q i (D.Z (i + 1) • D.Gint i - ofR (D.C (i + 1))) ≤ K * D.Mz (i + 1))
    (hrange : ∀ i, i + 1 < N → 2 * rng (D.Gint i) < L ^ (i + 1)) (hK : 0 ≤ K)
    {k j : ℕ} (hk1 : 1 ≤ k) (hkj : k ≤ j + 1) (hjN : j + 1 < N) :
    2 * rng (Cp D k) < L ^ k ∧
      (∑ x : Λ2, ‖kern (Cp D k) x‖ ≤ ((L : ℝ) ^ k) ^ 2 * (cS + K * D.Mz (j + 1))) ∧
      dopB (Cp D k) (cS + K * D.Mz (j + 1)) ((L : ℝ) ^ (k - 1)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL1 : 1 ≤ L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hkN : k < N := by omega
  have hr : 2 * rng (Cp D k) < L ^ k := by
    have h1 := hrange (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at h1
    have h4 : rng (Cp D k) ≤ rng (D.Gint (k - 1)) := rng_smul_le _ _
    omega
  have hcl := hclose (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at hcl
  have hMz : K * D.Mz k ≤ K * D.Mz (j + 1) := by gcongr; exact Mz_mono (by omega)
  have hCp : Cp D k = ofR (D.C k) + (Cp D k - ofR (D.C k)) := by abel
  have hδ : Cp D k - ofR (D.C k) = D.Z k • D.Gint (k - 1) - ofR (D.C k) := rfl
  refine ⟨hr, ?_, ?_⟩
  · refine kern_sum_le hr fun x => ?_
    rw [hCp, kern_add]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_kern_le_snorm hL0 q (k - 1) _ x).trans (std_c hS hL1 hk1 hkN)
    · rw [hδ]
      exact (norm_kern_le_snorm hL0 q (k - 1) _ x).trans (hcl.trans hMz)
  · rw [hCp]
    refine dopB_add (dopB_of_S4a hS (by omega) hk1 hkN) ?_
    rw [hδ]
    exact dopB_mono (dopB_of_snorm hq hcl) hMz (by positivity)

set_option maxHeartbeats 1000000 in
/-- **(HD).** -/
theorem HD : ∀ (L : ℕ) [NeZero L], 49 ≤ L → ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ KB : ℝ, 0 ≤ KB ∧
    ∀ (N : ℕ) (msq : ℝ) (ζ : ℕ → ℂ), 1 ≤ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
      (∀ i, ‖ζ i‖ ≤ ζbar) → ∀ j : ℕ, j + 1 < N → ∀ ℓ : ℝ, 0 ≤ ℓ →
      (∀ i ≤ j, GoodCov2 i ℓ (DressedFRD.kmat ((dData L N msq ζ).Gint i))) → ∀ κ : ℕ → Coup,
      ‖qTil (dData L N msq ζ) κ j‖ ≤ KB ∧
        ∑ k ∈ range j, ((j - k + 1 : ℕ) : ℝ) * 2 ^ (j - k) * ‖bTil (dData L N msq ζ) κ j k‖ ≤ KB := by
  obtain ⟨M₂, hM₂0, hS1⟩ := first_diff_le
  intro L _ hL
  obtain ⟨ζbar, hζ, hζ8, K, hK⟩ := thm_main_frd Pc (d := 2) le_rfl (q := 4) (by norm_num)
    (by omega : 7 ≤ L)
  obtain ⟨cS, hcS, hS⟩ := frd_stdFull Pc (d := 2) le_rfl (by omega : 7 ≤ L) (q := 4)
    (M := 4 + 2 + 1) le_rfl
  set K' := max K 0
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hKK : K ≤ K' := le_max_left _ _
  set Lr : ℝ := (L : ℝ)
  have hL0 : 0 < Lr := by simp only [Lr]; exact_mod_cast (by omega : 0 < L)
  have hLr : (49 : ℝ) ≤ Lr := by simp only [Lr]; exact_mod_cast hL
  set C₁ := (cS + K') * (28 * (cS + K') + 16 * (M₂ + K' / 2))
  set KB1 := Lr ^ 2 * (8 + 2 * Lr ^ 2 + 4 * Lr) * (cS + K') ^ 2
  have hC₁ : 0 ≤ C₁ := by positivity
  have hKB1 : 0 ≤ KB1 := by positivity
  refine ⟨ζbar, hζ, KB1 + Lr ^ 2 * C₁, by positivity,
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
  have hζ2 : ∀ i, ‖D.ζ i‖ ≤ 1 / 2 := fun i => (hζ8' i).trans (by norm_num)
  have hZ : ∀ i, D.Z i ≠ 0 := Z_ne_zero hζ2
  set Mz := D.Mz (j + 1)
  have hMz0 : 0 ≤ Mz := Mz_nonneg _
  have hMz : Mz ≤ 1 / 8 := Mz_le (by norm_num) fun i _ => hζ8' i
  have hKMz : K' * Mz ≤ K' := by nlinarith
  have hn : 2 * (L ^ (j + 1) + 4) < L ^ N := by
    have h1 : L ^ (j + 1) * L ≤ L ^ N := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) hjN
    have h2 : L ≤ L ^ (j + 1) := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : L ^ (j + 1) * 7 ≤ L ^ (j + 1) * L := Nat.mul_le_mul_left _ (by omega)
    omega
  have hρ : (1 : ℝ) ≤ Lr ^ j := one_le_pow₀ (by linarith)
  have hρ0 : 0 < Lr ^ j := by positivity
  obtain ⟨hrJ, hsumJ, hdJ⟩ := Cp_facts D hS' le_rfl hclose hrange hK'0 (k := j + 1) (j := j)
    (by omega) le_rfl hjN
  simp only [show j + 1 - 1 = j by omega] at hdJ
  have hrJR : rng (Cp D (j + 1)) ≤ L ^ (j + 1) := by omega
  constructor
  · -- `q̃`
    rw [qTil_eq D (by norm_num; omega) hjN hCs (hrange j hjN) κ]
    have hb := bubX_dop hn hrJR hrJR le_rfl hρ0 hdJ
    have hbr := bracket_le2 (M := cS + K' * Mz) (ρ := Lr ^ j) (Lr := Lr) (by positivity) hρ hL0.le
    have hR : ((L ^ (j + 1) : ℕ) : ℝ) = Lr * Lr ^ j := by simp only [Lr]; push_cast; ring
    rw [hR] at hb
    calc _ ≤ (∑ x : Lam 2 L N, ‖kern (Cp D (j + 1)) x‖) *
          ((cS + K' * Mz) * (8 + 2 * Lr ^ 2 + 4 * Lr) / (Lr ^ j) ^ 2) :=
          hb.trans (mul_le_mul_of_nonneg_left hbr (sum_nonneg fun _ _ => norm_nonneg _))
      _ ≤ ((Lr ^ (j + 1)) ^ 2 * (cS + K')) * ((cS + K') * (8 + 2 * Lr ^ 2 + 4 * Lr) / (Lr ^ j) ^ 2) := by
          gcongr
          · exact hsumJ.trans (by gcongr)
      _ = KB1 := by simp only [KB1]; field_simp; ring
      _ ≤ _ := by have : 0 ≤ Lr ^ 2 * C₁ := by positivity
                  linarith
  · -- the past
    have hS1j := hS1 L N (by omega) msq hm j hjN
    have hS1d := S1_dressed D le_rfl hK'0 hCs hclose hjN hS1j
    have hterm : ∀ k ∈ range j, ((j - k + 1 : ℕ) : ℝ) * 2 ^ (j - k) * ‖bTil D κ j k‖ ≤
        Lr ^ 2 * C₁ * (9 / (2 * Lr ^ 2)) ^ (j - k) := by
      intro k hk
      have hkj := mem_range.1 hk
      obtain ⟨hrK, hsumK, -⟩ := Cp_facts D hS' le_rfl hclose hrange hK'0 (k := k + 1) (j := j)
        (by omega) (by omega) hjN
      -- the ratio
      have hρ' : ‖D.Z (j + 1) / D.Z (k + 1)‖ ≤ (9 / 8) ^ (j - k) := by
        have e := Z_ratio_eq D hζ2 (k := k + 1) (j := j) (by omega)
        have hb' := prod_one_add_bounds (Ico (k + 1) (j + 1)) D.ζ hMz0
          (fun i hi => norm_le_Mz (mem_Ico.1 hi).2)
        rw [Nat.card_Ico, show j + 1 - (k + 1) = j - k by omega] at hb'
        rw [e]
        exact hb'.1.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
      -- the bubble
      have hbub : ‖bubX (cKer (L ^ (j + 1)) (Cp D (k + 1))) (cKer (L ^ (j + 1)) (Cp D (j + 1)))‖ ≤
          (Lr ^ (k + 1)) ^ 2 * (cS + K') * (14 * (cS + K') / (Lr ^ j) ^ 2) := by
        have hrk : rng (Cp D (k + 1)) ≤ L ^ (k + 1) := by omega
        have hb := bubX_dop hn hrJR hrk (Nat.pow_le_pow_right (by omega) (by omega)) hρ0 hdJ
        have hbr := bracket_le (M := cS + K' * Mz) (ρ := Lr ^ j) (R' := ((L ^ (k + 1) : ℕ) : ℝ))
          (by positivity) hρ (by positivity)
          (by push_cast; exact pow_le_pow_right₀ (by linarith) (by omega))
        calc _ ≤ (∑ x : Lam 2 L N, ‖kern (Cp D (k + 1)) x‖) * (14 * (cS + K' * Mz) / (Lr ^ j) ^ 2) :=
              hb.trans (mul_le_mul_of_nonneg_left (by push_cast at hbr ⊢; exact hbr)
                (sum_nonneg fun _ _ => norm_nonneg _))
          _ ≤ _ := by
              gcongr
              · exact hsumK.trans (by gcongr)
      -- the zero mode
      have h0 : ‖Cp D (k + 1) 0‖ ≤ (Lr ^ (k + 1)) ^ 2 * (cS + K') := by
        rw [← sum_kern_eq (Cp D (k + 1))]
        exact (norm_sum_le _ _).trans (hsumK.trans (by gcongr))
      have hS1' : ‖kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Lam 2 L N) - kern (Cp D (j + 1)) 0‖ ≤
          (M₂ + K' / 2) / (Lr ^ j) ^ 2 := hS1d.trans (by gcongr)
      have hq : (Lr ^ (k + 1)) ^ 2 / (Lr ^ j) ^ 2 = Lr ^ 2 * (1 / Lr ^ 2) ^ (j - k) := by
        obtain ⟨t, ht⟩ : ∃ t, j = k + 1 + t := ⟨j - k - 1, by omega⟩
        rw [ht, show k + 1 + t - k = t + 1 by omega, one_div_pow]
        field_simp
        ring
      have hbe := bTil_eq D (by norm_num; omega) hkj hjN hCs (fun k hk => hrange k (by omega)) hZ
        hℓ hG κ
      have hnorm : ‖bTil D κ j k‖ ≤ (9 / 8) ^ (j - k) * (C₁ * (Lr ^ 2 * (1 / Lr ^ 2) ^ (j - k))) := by
        rw [hbe, norm_mul]
        refine mul_le_mul hρ' ?_ (norm_nonneg _) (by positivity)
        calc ‖2 * bubX (cKer (L ^ (j + 1)) (Cp D (k + 1))) (cKer (L ^ (j + 1)) (Cp D (j + 1))) +
              16 * (kern (Cp D (j + 1)) (dirVec (Sum.inl 0)) - kern (Cp D (j + 1)) 0) * Cp D (k + 1) 0‖
            ≤ 2 * ‖bubX (cKer (L ^ (j + 1)) (Cp D (k + 1))) (cKer (L ^ (j + 1)) (Cp D (j + 1)))‖ +
              16 * ‖kern (Cp D (j + 1)) (dirVec (Sum.inl 0) : Lam 2 L N) - kern (Cp D (j + 1)) 0‖ *
                ‖Cp D (k + 1) 0‖ := by
              refine (norm_add_le _ _).trans (le_of_eq ?_)
              rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat]
          _ ≤ 2 * ((Lr ^ (k + 1)) ^ 2 * (cS + K') * (14 * (cS + K') / (Lr ^ j) ^ 2)) +
              16 * ((M₂ + K' / 2) / (Lr ^ j) ^ 2) * ((Lr ^ (k + 1)) ^ 2 * (cS + K')) := by
              gcongr
          _ = C₁ * ((Lr ^ (k + 1)) ^ 2 / (Lr ^ j) ^ 2) := by simp only [C₁]; field_simp; ring
          _ = _ := by rw [hq]
      have hw : ((j - k + 1 : ℕ) : ℝ) * 2 ^ (j - k) ≤ 2 ^ (j - k) * 2 ^ (j - k) := by
        gcongr; exact succ_le_two_pow (j - k)
      calc ((j - k + 1 : ℕ) : ℝ) * 2 ^ (j - k) * ‖bTil D κ j k‖
          ≤ (2 ^ (j - k) * 2 ^ (j - k)) * ((9 / 8) ^ (j - k) * (C₁ * (Lr ^ 2 * (1 / Lr ^ 2) ^ (j - k)))) :=
            mul_le_mul hw hnorm (norm_nonneg _) (by positivity)
        _ = Lr ^ 2 * C₁ * (2 * 2 * (9 / 8) * (1 / Lr ^ 2)) ^ (j - k) := by
            rw [mul_pow, mul_pow, mul_pow]; ring
        _ = Lr ^ 2 * C₁ * (9 / (2 * Lr ^ 2)) ^ (j - k) := by congr 2; field_simp; ring
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum]
    have hx : 9 / (2 * Lr ^ 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have := geom_half_le (x := 9 / (2 * Lr ^ 2)) (by positivity) hx j
    have hp : 0 ≤ Lr ^ 2 * C₁ := by positivity
    calc Lr ^ 2 * C₁ * ∑ k ∈ range j, (9 / (2 * Lr ^ 2)) ^ (j - k) ≤ Lr ^ 2 * C₁ * 1 := by gcongr
      _ ≤ _ := by linarith

end

end Step2