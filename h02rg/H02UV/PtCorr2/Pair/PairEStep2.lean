import PtCorr2.Pair.VObsStepAB2

/-!
# The `M₄` seed weights with a growing field scale

`m4_hist_weighted_sizes` (`PtCorr2.Pair.VObsStepAB2`) needs a nonincreasing `ℓ`; the field scale
`s_k = histS` of the history is not monotone (`s_{k+1} = s_k·fscale(1 + ζ_k)`), but
`s_{k+1} ≤ (1 + ρ)s_k` (`histS_ratio_le`). Copies with `ℓ_k ≤ q^{k-i}ℓ_i`, `q⁴L^{-2} ≤ 1/4`:
**`m4_kernel_le_q`**, **`m4_weighted_sum_le_q`** (same constant `16`),
**`m4_hist_weighted_le_q`**, **`m4_hist_weighted_sizes_q`** (`σ_k = K_{M4}(q⁴κ^Q_k + κ^S_k)`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

section Pure

/-- One term of the kernel with a growing field scale (`ℓ_k ≤ q^{k-1-i}ℓ_{i+1}`):
`ℓ_{i+1}^{-4}(L^{i+1}/s)²·2ℓ_k²(L^{j_x+1}ℓ_k/L^{k+1})² ≤ 8(q⁴L^{-2})^{k-1-i}`. -/
theorem m4_kernel_le_q (hL : (2 : ℝ) ≤ L) {jx i k : ℕ} (hik : i < k) {s : ℝ} (hs0 : 0 < s)
    (hs : (L : ℝ) ^ jx ≤ 2 * s) {q : ℝ} (hq : 1 ≤ q) {ℓi ℓk : ℝ} (hℓi : 0 < ℓi) (hℓk : 0 < ℓk)
    (hℓ : ℓk ≤ q ^ (k - 1 - i) * ℓi) :
    ℓi⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) *
        (2 * ℓk ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓk / (L : ℝ) ^ (k + 1))) ^ 2) ≤
      8 * (q ^ 4 * ((L : ℝ) ^ 2)⁻¹) ^ (k - 1 - i) := by
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨m, rfl⟩ : ∃ m, k = i + 1 + m := ⟨k - (i + 1), by omega⟩
  rw [show i + 1 + m - 1 - i = m by omega] at hℓ ⊢
  set A : ℝ := (L : ℝ) ^ (i + 1)
  set Lj : ℝ := (L : ℝ) ^ jx
  set Lm : ℝ := (L : ℝ) ^ m
  have hA : 0 < A := pow_pos hL0 _
  have hLj : 0 < Lj := pow_pos hL0 _
  have hLm : 0 < Lm := pow_pos hL0 _
  have e1 : (L : ℝ) ^ (i + 1 + m + 1) = A * Lm * L := by
    rw [show i + 1 + m + 1 = (i + 1) + m + 1 by ring, pow_succ, pow_add]
  have e2 : (L : ℝ) ^ (jx + 1) = Lj * L := pow_succ _ _
  have e3 : (((L : ℝ) ^ 2)⁻¹) ^ m = (Lm ^ 2)⁻¹ := by
    rw [inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  have e4 : (q ^ 4 * ((L : ℝ) ^ 2)⁻¹) ^ m = (q ^ m) ^ 4 * (Lm ^ 2)⁻¹ := by
    rw [mul_pow, e3]; ring
  rw [e1, e2, e4]
  have e : ℓi⁻¹ ^ 4 * (A ^ 2 / s ^ 2) * (2 * ℓk ^ 2 * (Lj * L * (ℓk / (A * Lm * L))) ^ 2) =
      2 * (ℓk / ℓi) ^ 4 * (Lj / s) ^ 2 * (Lm ^ 2)⁻¹ := by
    field_simp
  rw [e]
  have hqm : 0 ≤ q ^ m := pow_nonneg (by linarith) m
  have h1 : (ℓk / ℓi) ^ 4 ≤ (q ^ m) ^ 4 :=
    pow_le_pow_left₀ (div_nonneg hℓk.le hℓi.le) ((div_le_iff₀ hℓi).2 hℓ) 4
  have h2 : (Lj / s) ^ 2 ≤ 4 := by
    have : Lj / s ≤ 2 := (div_le_iff₀ hs0).2 (by linarith)
    have h0 : 0 ≤ Lj / s := div_nonneg hLj.le hs0.le
    nlinarith
  have h3 : 0 ≤ (Lm ^ 2)⁻¹ := by positivity
  have h4 : 0 ≤ (ℓk / ℓi) ^ 4 := by positivity
  calc 2 * (ℓk / ℓi) ^ 4 * (Lj / s) ^ 2 * (Lm ^ 2)⁻¹ ≤ 2 * (q ^ m) ^ 4 * 4 * (Lm ^ 2)⁻¹ := by
        gcongr
    _ = 8 * ((q ^ m) ^ 4 * (Lm ^ 2)⁻¹) := by ring

/-- **`m4_weighted_sum_le` with a growing field scale**: `ℓ_k ≤ q^{k-i}ℓ_i`, `q⁴L^{-2} ≤ 1/4`
(instead of `ℓ` nonincreasing). -/
theorem m4_weighted_sum_le_q (hL : (2 : ℝ) ≤ L) {jx : ℕ} {s : ℝ} (hs0 : 0 < s)
    (hs : (L : ℝ) ^ jx ≤ 2 * s) (ℓ : ℕ → ℝ) (hℓ : ∀ k, 0 < ℓ k) {q : ℝ} (hq : 1 ≤ q)
    (hqL : q ^ 4 * ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 4)
    (hℓm : ∀ i k, i ≤ k → ℓ k ≤ q ^ (k - i) * ℓ i) {M : ℕ → ℂ} (h0 : M jx = 0) (σ : ℕ → ℝ)
    (hσ : ∀ k, 0 ≤ σ k)
    (n : ℕ) (hstep : ∀ k, jx ≤ k → k < n → ‖M (k + 1) - M k‖ ≤
      (ℓ (k + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (k + 1)) ^ 2 / s ^ 2) * σ k) :
    ∑ k ∈ Ico jx n, ‖M k‖ * (2 * ℓ k ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓ k / (L : ℝ) ^ (k + 1))) ^ 2) ≤
      16 * ∑ k ∈ Ico jx n, σ k := by
  have hL0 : (0 : ℝ) < L := by linarith
  set qq : ℝ := q ^ 4 * ((L : ℝ) ^ 2)⁻¹ with hqq
  have hq0 : 0 ≤ qq := by have : (0 : ℝ) ≤ q := by linarith
                          positivity
  have hq1 : qq ≤ 1 / 4 := hqL
  set w : ℕ → ℝ := fun k => 2 * ℓ k ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓ k / (L : ℝ) ^ (k + 1))) ^ 2
  have hw : ∀ k, 0 ≤ w k := fun k => by
    have := hℓ k; have : 0 < (L : ℝ) ^ (k + 1) := pow_pos hL0 _; positivity
  have hM := m4_norm_le_sum h0 _ hstep
  have step1 : ∀ k ∈ Ico jx n, ‖M k‖ * w k ≤ ∑ i ∈ Ico jx k, 8 * qq ^ (k - 1 - i) * σ i := by
    intro k hk
    have hjk := (mem_Ico.1 hk).1
    refine (mul_le_mul_of_nonneg_right (hM k hjk (mem_Ico.1 hk).2.le) (hw k)).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun i hi => ?_
    have hik := (mem_Ico.1 hi).2
    have hker := m4_kernel_le_q hL hik hs0 hs hq (hℓ (i + 1)) (hℓ k)
      (by have := hℓm (i + 1) k (by omega); rwa [show k - (i + 1) = k - 1 - i by omega] at this)
    calc (ℓ (i + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) * σ i * w k
        = ((ℓ (i + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) * w k) * σ i := by ring
      _ ≤ (8 * qq ^ (k - 1 - i)) * σ i := mul_le_mul_of_nonneg_right hker (hσ i)
  have step2 : ∑ k ∈ Ico jx n, ∑ i ∈ Ico jx k, 8 * qq ^ (k - 1 - i) * σ i =
      ∑ i ∈ Ico jx n, ∑ k ∈ Ico (i + 1) n, 8 * qq ^ (k - 1 - i) * σ i := by
    refine sum_comm' fun k i => ?_
    simp only [mem_Ico]; omega
  have hgeo : ∀ i, ∑ k ∈ Ico (i + 1) n, qq ^ (k - 1 - i) ≤ 4 / 3 := by
    intro i
    rw [sum_Ico_eq_sum_range]
    have e : ∀ k ∈ range (n - (i + 1)), qq ^ (i + 1 + k - 1 - i) = qq ^ k := fun k _ => by
      rw [show i + 1 + k - 1 - i = k by omega]
    rw [sum_congr rfl e]
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n - (i + 1)) hq0 (by linarith)
    rw [← range_eq_Ico, pow_zero] at h
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]; linarith
  calc ∑ k ∈ Ico jx n, ‖M k‖ * w k
      ≤ ∑ k ∈ Ico jx n, ∑ i ∈ Ico jx k, 8 * qq ^ (k - 1 - i) * σ i := sum_le_sum step1
    _ = ∑ i ∈ Ico jx n, ∑ k ∈ Ico (i + 1) n, 8 * qq ^ (k - 1 - i) * σ i := step2
    _ = ∑ i ∈ Ico jx n, 8 * σ i * ∑ k ∈ Ico (i + 1) n, qq ^ (k - 1 - i) := by
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    _ ≤ ∑ i ∈ Ico jx n, 8 * σ i * (4 / 3) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hgeo i) (by have := hσ i; positivity)
    _ ≤ ∑ i ∈ Ico jx n, 16 * σ i := sum_le_sum fun i _ => by have := hσ i; nlinarith
    _ = 16 * ∑ k ∈ Ico jx n, σ k := by rw [mul_sum]


end Pure

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (j : ℕ)
  (o' : ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- **`m4_hist_weighted_le` with a growing field scale** (`ℓ_k ≤ q^{k-i}ℓ_i`). -/
theorem m4_hist_weighted_le_q (hL : (2 : ℝ) ≤ L) (h0 : ObsVabInv P o')
    (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0) {n : ℕ}
    (hs : ∀ k, j ≤ k → k < n → ObsSymInv k (obsHistFrom R P j o' k t))
    {s : ℝ} (hs0 : 0 < s) (hsj : (L : ℝ) ^ j ≤ 2 * s) (ℓ : ℕ → ℝ) (hℓ : ∀ k, 0 < ℓ k)
    {q : ℝ} (hq : 1 ≤ q) (hqL : q ^ 4 * ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 4)
    (hℓm : ∀ i k, i ≤ k → ℓ k ≤ q ^ (k - i) * ℓ i) (σ : ℕ → ℝ) (hσ : ∀ k, 0 ≤ σ k)
    (hsrc : ∀ k, j ≤ k → k < n →
      ∑ b ∈ blockIdx (L := L) (N := N) k,
          ‖cfAB4 P.a P.b (Q2O P k (hKR R P j o' t k) b : SA .two (Lam 2 L N)).ab‖ +
        ∑ b ∈ blockIdx (L := L) (N := N) k,
          ‖cfAB4 P.a P.b (LSO P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) b :
            SA .two (Lam 2 L N)).ab‖ ≤
        (ℓ (k + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (k + 1)) ^ 2 / s ^ 2) * σ k) :
    ∑ k ∈ Finset.Ico j n, ‖m4Tot P k (hVR R P j o' t k)‖ *
        (2 * ℓ k ^ 2 * ((L : ℝ) ^ (j + 1) * (ℓ k / (L : ℝ) ^ (k + 1))) ^ 2) ≤
      16 * ∑ k ∈ Finset.Ico j n, σ k := by
  refine m4_weighted_sum_le_q hL hs0 hsj ℓ hℓ hq hqL hℓm (m4Tot_hVR_start R P j o' t hz) σ hσ n
    fun k hk hkn => ?_
  rw [m4Tot_hVR_succ R P j o' t h0 hk (hs k hk hkn)]
  have e : ∀ x y z : ℂ, x - y - z - x = -(y + z) := fun x y z => by ring
  rw [e, norm_neg]
  exact (norm_add_le _ _).trans
    (le_trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _)) (hsrc k hk hkn))

/-- **`m4_hist_weighted_sizes` with a growing field scale** (`ℓ_k ≤ q^{k-i}ℓ_i`,
`q⁴L^{-2} ≤ 1/4`): `σ_k = K_{M4}(q⁴κ^Q_k + κ^S_k)`. -/
theorem m4_hist_weighted_sizes_q (hL2 : (2 : ℝ) ≤ L) {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin 2 → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir 2 → ℕ,
      Grassmann.mabs α ≤ pPhi 2 → ∀ u : Zd 2,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hab : P.a ≠ P.b) (h0 : ObsVabInv P o')
    (hz : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0) {n : ℕ} (hnN : n + 1 ≤ N)
    (hs : ∀ k, j ≤ k → k < n → ObsSymInv k (obsHistFrom R P j o' k t))
    (hsj : (L : ℝ) ^ j ≤ 2 * ((supNorm (P.a - P.b) : ℕ) : ℝ))
    (ℓ : ℕ → ℝ) (hℓ : ∀ k, 0 < ℓ k) {q : ℝ} (hq : 1 ≤ q)
    (hqL : q ^ 4 * ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 4) (hℓm : ∀ i k, i ≤ k → ℓ k ≤ q ^ (k - i) * ℓ i)
    (hKl : ∀ k, j ≤ k → k < n → ∀ X, IsSmall k X →
      (hKR R P j o' t k X : SA .two (Lam 2 L N)).ab ∈ NX (nbhd k X : Set (Lam 2 L N)))
    (hSl : ∀ k, j ≤ k → k < n → ∀ b ∈ blockIdx (L := L) (N := N) k,
      (SXO k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k)
        (Step2.Bp (L := L) (N := N) k b) : SA .two (Lam 2 L N)).ab ∈
        NX (nbhd (k + 1) (Step2.Bp (L := L) (N := N) k b) : Set (Lam 2 L N)))
    (κQ κS : ℕ → ℝ) (hκQ0 : ∀ k, 0 ≤ κQ k) (hκS0 : ∀ k, 0 ≤ κS k)
    (hκQ : ∀ k, j ≤ k → k < n →
      (open Classical in ∑ b ∈ blockIdx (L := L) (N := N) k,
        ∑ X ∈ (smallSets k).filter (fun X => blockSet k b ⊆ X),
          (Tj 2 (L : ℝ) k (ℓ k) (hKR R P j o' t k X : SA .two (Lam 2 L N)).ab).toReal) ≤ κQ k)
    (hκS : ∀ k, j ≤ k → k < n →
      ∑ b ∈ blockIdx (L := L) (N := N) k,
        (Tj 2 (L : ℝ) (k + 1) (ℓ (k + 1))
          (SXO k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k)
            (Step2.Bp (L := L) (N := N) k b) : SA .two (Lam 2 L N)).ab).toReal ≤ κS k) :
    ∑ k ∈ Finset.Ico j n, ‖m4Tot P k (hVR R P j o' t k)‖ *
        (2 * ℓ k ^ 2 * ((L : ℝ) ^ (j + 1) * (ℓ k / (L : ℝ) ^ (k + 1))) ^ 2) ≤
      16 * ∑ k ∈ Finset.Ico j n, KM4 2 Cc * (q ^ 4 * κQ k + κS k) := by
  classical
  set s : ℝ := ((supNorm (P.a - P.b) : ℕ) : ℝ)
  have hs0 : 0 < s := by
    have : supNorm (P.a - P.b) ≠ 0 := fun h0 =>
      hab (sub_eq_zero.1 ((supNorm_eq_zero_iff _).1 h0))
    show (0 : ℝ) < ((supNorm (P.a - P.b) : ℕ) : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero this
  have hK := KM4_nonneg 2 (Cc := Cc)
  have hL0 : (0 : ℝ) < L := by linarith
  have hq0 : (0 : ℝ) ≤ q := by linarith
  refine m4_hist_weighted_le_q R P j o' t hL2 h0 hz hs hs0 hsj ℓ hℓ hq hqL hℓm _
    (fun k => mul_nonneg hK (add_nonneg (mul_nonneg (pow_nonneg hq0 4) (hκQ0 k)) (hκS0 k)))
    fun k hk hkn => ?_
  set u : ℝ := (ℓ (k + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (k + 1)) ^ 2 / s ^ 2) with hu
  have hu0 : 0 ≤ u := by have := hℓ (k + 1); positivity
  have hQu : (ℓ k)⁻¹ ^ 4 * (((L : ℝ) ^ k) ^ 2 / s ^ 2) ≤ q ^ 4 * u := by
    have h1 : (ℓ k)⁻¹ ^ 4 ≤ q ^ 4 * (ℓ (k + 1))⁻¹ ^ 4 := by
      have h5 := hℓm k (k + 1) (by omega)
      rw [show k + 1 - k = 1 by omega, pow_one] at h5
      have h6 : (ℓ k)⁻¹ ≤ q * (ℓ (k + 1))⁻¹ := by
        rw [inv_le_comm₀ (hℓ k) (mul_pos (by linarith) (inv_pos.2 (hℓ (k + 1)))), mul_inv, inv_inv]
        calc q⁻¹ * ℓ (k + 1) ≤ q⁻¹ * (q * ℓ k) :=
              mul_le_mul_of_nonneg_left h5 (inv_nonneg.2 hq0)
          _ = ℓ k := by field_simp
      calc (ℓ k)⁻¹ ^ 4 ≤ (q * (ℓ (k + 1))⁻¹) ^ 4 :=
            pow_le_pow_left₀ (inv_nonneg.2 (hℓ k).le) h6 4
        _ = q ^ 4 * (ℓ (k + 1))⁻¹ ^ 4 := by ring
    have h2 : ((L : ℝ) ^ k) ^ 2 / s ^ 2 ≤ ((L : ℝ) ^ (k + 1)) ^ 2 / s ^ 2 := by
      have : (L : ℝ) ^ k ≤ (L : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by linarith) (by omega)
      have h3 : 0 ≤ (L : ℝ) ^ k := by positivity
      gcongr
    calc (ℓ k)⁻¹ ^ 4 * (((L : ℝ) ^ k) ^ 2 / s ^ 2)
        ≤ (q ^ 4 * (ℓ (k + 1))⁻¹ ^ 4) * (((L : ℝ) ^ (k + 1)) ^ 2 / s ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by have := hℓ (k + 1); positivity)
      _ = q ^ 4 * u := by rw [hu]; ring
  have hQ : ∑ b ∈ blockIdx (L := L) (N := N) k,
      ‖cfAB4 P.a P.b (Q2O P k (hKR R P j o' t k) b : SA .two (Lam 2 L N)).ab‖ ≤
        u * (KM4 2 Cc * (q ^ 4 * κQ k)) := by
    refine (sum_le_sum fun b _ => norm_cfAB4_Q2O_le hCc0 hCc hL P hab k (hKR R P j o' t k)
      (hKl k hk hkn) b (hℓ k)).trans ?_
    rw [← mul_sum]
    set S := ∑ b ∈ blockIdx (L := L) (N := N) k,
        ∑ X ∈ (smallSets k).filter (fun X => blockSet k b ⊆ X),
          (Tj 2 (L : ℝ) k (ℓ k) (hKR R P j o' t k X : SA .two (Lam 2 L N)).ab).toReal with hSd
    have hsum0 : 0 ≤ S := sum_nonneg fun _ _ => sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have e2 : KM4 2 Cc * (ℓ k)⁻¹ ^ 4 * (((L : ℝ) ^ k) ^ 2 / s ^ 2) * S =
        KM4 2 Cc * ((ℓ k)⁻¹ ^ 4 * (((L : ℝ) ^ k) ^ 2 / s ^ 2)) * S := by ring
    rw [e2]
    calc KM4 2 Cc * ((ℓ k)⁻¹ ^ 4 * (((L : ℝ) ^ k) ^ 2 / s ^ 2)) * S
        ≤ KM4 2 Cc * (q ^ 4 * u) * κQ k :=
          mul_le_mul (mul_le_mul_of_nonneg_left hQu hK) (hκQ k hk hkn) hsum0
            (mul_nonneg hK (mul_nonneg (pow_nonneg hq0 4) hu0))
      _ = u * (KM4 2 Cc * (q ^ 4 * κQ k)) := by ring
  have hS : ∑ b ∈ blockIdx (L := L) (N := N) k,
      ‖cfAB4 P.a P.b (LSO P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) b :
        SA .two (Lam 2 L N)).ab‖ ≤ u * (KM4 2 Cc * κS k) := by
    refine (sum_le_sum fun b hb => norm_cfAB4_LSO_le hCc0 hCc hL P hab (by omega) _ _ _ hb
      (hSl k hk hkn b hb) (hℓ (k + 1))).trans ?_
    rw [← mul_sum]
    have e3 : ∀ T : ℝ, KM4 2 Cc * (ℓ (k + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (k + 1)) ^ 2 / s ^ 2) * T =
        KM4 2 Cc * u * T := fun T => by rw [hu]; ring
    rw [e3]
    calc KM4 2 Cc * u * _ ≤ KM4 2 Cc * u * κS k :=
          mul_le_mul_of_nonneg_left (hκS k hk hkn) (mul_nonneg hK hu0)
      _ = u * (KM4 2 Cc * κS k) := by ring
  calc _ ≤ u * (KM4 2 Cc * (q ^ 4 * κQ k)) + u * (KM4 2 Cc * κS k) := add_le_add hQ hS
    _ = u * (KM4 2 Cc * (q ^ 4 * κQ k + κS k)) := by ring


end Hist

end

end PtCorr2
