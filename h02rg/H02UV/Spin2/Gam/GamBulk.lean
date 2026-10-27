import Spin2.Case2.Case2Thm
import Spin2.Gam.GamRem
import Obs2.Flow.GamBulk

/-!
# `GamBulkRel` along the bulk flow (at every point `a`)

The bulk one-loop factor `E_k(a) = ε(F_{C_k}(ψ̄_aψ_a, V_{κ'_k}(Λ)))` (`κ' = kapH`) is, by
`Obs2.eps_FC_pbp_Vcoup`, `ν'_k∑_xC_k(a,x)C_k(x,a) + (y'_k + z'_k)𝔩_{C_k}(a)`, with
`y' + z' = z_k + y_k - Z_kζ_k - g_k(c₀_k + δ_k)` (`kapH_yz`; the clamp `Y_c` cancels).
Along a history with the bulk context `C2Ctx` and `|z_k + y_k| ≤ 2c_zǧ_k|Z_k|`:

* `k ≥ 1` (`gamBulk_le_pos`): `‖E_k‖ ≤ K_b ǧ_k/|Z_{k+1}|`, `K_b = L²ℓ⁴(c_μ + 3c_z) + ℓ⁶ + c_zℓ⁴`
  (Gram bounds at `ℓ_k² = ℓ²/(16|Z_{k+1}|)`: `ν' = O(ǧ|Z|L^{-2k})`, `y' + z' = O(ǧ|Z|)`);
* `k = 0` (`gamBulk_le_zero`): `Z_1 = 1`, `C_0 = C_1` is the bare covariance with a nonnegative
  symbol (`frdC_nonneg`), so `|C_0(x,y)| ≤ C_0(0,0) = Γ^{int}_1(0,0)` and
  `‖E_0‖ ≤ K_0ǧ_0‖Γ^{int}_1(0,0)‖`;
* the lower bound `|Z_{k+1}Γ^{int}_{k+1}(0,0)| ≥ 1` for `1 ≤ k < N_h` (`gamInt_lower`), from the
  value `C'_{k+1}(0,0) = log L/2π + O(L^{-2k} + m²L^{2(k+1)}) + O(M_z)` (`Step2.D2.Cprime_values`)
  if `log L ≥ gbLog` and `K_C·2cε ≤ 1`, `2cε ≤ ζ̄`.

Hence **`GamBulkRelA`** (the bound at every point `a`, so both the pair (`a = 0`) and the mirrored
(`a = x`) histories are covered) with `c_e = gbK = K_b + K_0`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L N : ℕ} [NeZero L]

/-! ### The statement at every point -/

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `E_k(a) = ε(F_{C_k}(ψ̄_aψ_a, V_{κ'_k}(Λ)))` along the trajectory. -/
def gamBulkA (m b μ₀ : ℝ) (a : Lam 2 L N) (k : ℕ) : ℂ :=
  ε (FC (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) (Obs.LocObs.pbp a)
    (Vcoup (Obs2.kapH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) univ))

/-- **`GamBulkRel` at every point `a`**. -/
def GamBulkRelA (Nh : ℕ) (m b μ₀ ce : ℝ) : Prop :=
  ∀ a : Lam 2 L N, ∀ k < Nh, ‖gamBulkA R m b μ₀ a k‖ ≤
    ce * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) * ‖gamT R m b μ₀ k‖

theorem gamBulkRel_of_A {Nh : ℕ} {m b μ₀ ce : ℝ} (h : GamBulkRelA R Nh m b μ₀ ce) :
    GamBulkRel R Nh m b μ₀ ce := fun k hk => h 0 k hk

end Traj

/-! ### The couplings of `κ'` -/

section Coup

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (t : Hist.Seq (Xs R))

theorem kapH_yz (k : ℕ) :
    (Obs2.kapH R t k).y + (Obs2.kapH R t k).z =
      (rawHist R k t).z + (rawHist R k t).y - stA R (rawHist R k t) -
        Obs2.gH R t k * (Obs2.c0H R t k + Obs2.dlH R t k) := by
  simp only [Obs2.kapH, Coup.shift, Coup.ofVec]
  simp only [Matrix.cons_val]
  ring

/-- **`E_k(a) = ν'_k∑_xC_k(a,x)C_k(x,a) + (y'_k + z'_k)𝔩_{C_k}(a)`.** -/
theorem eps_hist_eq (k : ℕ) (a : Lam 2 L N) :
    ε (FC (Obs2.histCovO R t k) (Obs.LocObs.pbp a) (Vcoup (Obs2.kapH R t k) univ)) =
      (Obs2.kapH R t k).nu * ∑ x, Obs2.histCovO R t k a x * Obs2.histCovO R t k x a +
        ((rawHist R k t).z + (rawHist R k t).y - stA R (rawHist R k t) -
          Obs2.gH R t k * (Obs2.c0H R t k + Obs2.dlH R t k)) *
          Obs2.lfunC (Obs2.histCovO R t k) a := by
  rw [Obs2.eps_FC_pbp_Vcoup, kapH_yz]

end Coup

/-! ### The real-number algebra -/

/-- `k ≥ 1`. -/
theorem gb_alg_pos {nu T yz lf zp s g h2 L2 ℓ cmu cz : ℝ} (hzp : 0 < zp) (hg : 0 ≤ g)
    (hh2 : 0 < h2) (hL2 : 0 ≤ L2) (hcmu : 0 ≤ cmu) (hcz : 0 ≤ cz)
    (hs : s = ℓ ^ 2 / (16 * zp))
    (hnu : nu ≤ zp * L2 / h2 * ((cmu + 16 / 7 * cz) * g) + 16 / 7 * g * zp ^ 2 * s / h2)
    (hT : T ≤ 9 * h2 * (s * s)) (hyz : yz ≤ 32 / 7 * cz * g * zp + 16 / 7 * g * zp ^ 2 * s)
    (hlf : lf ≤ 18 * (s * s)) (hnu0 : 0 ≤ nu) (hyz0 : 0 ≤ yz) (hT0 : 0 ≤ T) (hlf0 : 0 ≤ lf) :
    nu * T + yz * lf ≤ (L2 * ℓ ^ 4 * (cmu + 3 * cz) + ℓ ^ 6 + cz * ℓ ^ 4) * g / zp := by
  have hA := mul_le_mul hnu hT hT0 (hnu0.trans hnu)
  have hB := mul_le_mul hyz hlf hlf0 (hyz0.trans hyz)
  have e : (zp * L2 / h2 * ((cmu + 16 / 7 * cz) * g) + 16 / 7 * g * zp ^ 2 * s / h2) *
      (9 * h2 * (s * s)) + (32 / 7 * cz * g * zp + 16 / 7 * g * zp ^ 2 * s) * (18 * (s * s)) =
      g / zp * (9 / 256 * L2 * ℓ ^ 4 * cmu + 9 / 256 * 16 / 7 * L2 * ℓ ^ 4 * cz +
        (144 / 7 + 288 / 7) / 4096 * ℓ ^ 6 + 576 / 7 / 256 * cz * ℓ ^ 4) := by
    rw [hs]; field_simp; ring
  have hK : 9 / 256 * L2 * ℓ ^ 4 * cmu + 9 / 256 * 16 / 7 * L2 * ℓ ^ 4 * cz +
        (144 / 7 + 288 / 7) / 4096 * ℓ ^ 6 + 576 / 7 / 256 * cz * ℓ ^ 4 ≤
      L2 * ℓ ^ 4 * (cmu + 3 * cz) + ℓ ^ 6 + cz * ℓ ^ 4 := by
    have hd : L2 * ℓ ^ 4 * (cmu + 3 * cz) + ℓ ^ 6 + cz * ℓ ^ 4 -
        (9 / 256 * L2 * ℓ ^ 4 * cmu + 9 / 256 * 16 / 7 * L2 * ℓ ^ 4 * cz +
          (144 / 7 + 288 / 7) / 4096 * ℓ ^ 6 + 576 / 7 / 256 * cz * ℓ ^ 4) =
        247 / 256 * (L2 * ℓ ^ 4 * cmu) + (3 - 9 / 256 * 16 / 7) * (L2 * ℓ ^ 4 * cz) +
          (1 - (144 / 7 + 288 / 7) / 4096) * ℓ ^ 6 + (1 - 576 / 7 / 256) * (cz * ℓ ^ 4) := by
      ring
    have : 0 ≤ 247 / 256 * (L2 * ℓ ^ 4 * cmu) + (3 - 9 / 256 * 16 / 7) * (L2 * ℓ ^ 4 * cz) +
          (1 - (144 / 7 + 288 / 7) / 4096) * ℓ ^ 6 + (1 - 576 / 7 / 256) * (cz * ℓ ^ 4) := by
      have : 0 ≤ ℓ ^ 6 := by positivity
      have : 0 ≤ ℓ ^ 4 := by positivity
      norm_num
      positivity
    linarith
  have hgz : 0 ≤ g / zp := div_nonneg hg hzp.le
  calc nu * T + yz * lf ≤ _ := add_le_add hA hB
    _ = _ := e
    _ ≤ g / zp * (L2 * ℓ ^ 4 * (cmu + 3 * cz) + ℓ ^ 6 + cz * ℓ ^ 4) :=
        mul_le_mul_of_nonneg_left hK hgz
    _ = _ := by ring

/-- `k = 0` (`Z_1 = 1`, `L2 = L²`, entry bound `c₀`). -/
theorem gb_alg_zero {nu T yz lf s g L ℓ cmu cz c₀ : ℝ} (hg : 0 ≤ g) (hL : 0 < L)
    (hcmu : 0 ≤ cmu) (hcz : 0 ≤ cz) (hc₀ : 0 ≤ c₀) (hs : s = ℓ ^ 2 / 16)
    (hnu : nu ≤ (cmu + 16 / 7 * cz) * g + 16 / 7 * g * s / L ^ 2)
    (hT : T ≤ 9 * L ^ 2 * (s * c₀)) (hyz : yz ≤ 32 / 7 * cz * g + 16 / 7 * g * s)
    (hlf : lf ≤ 18 * L ^ 2 * (s / L * (2 * c₀))) (hnu0 : 0 ≤ nu) (hyz0 : 0 ≤ yz)
    (hT0 : 0 ≤ T) (hlf0 : 0 ≤ lf) :
    nu * T + yz * lf ≤
      (L ^ 2 * ℓ ^ 2 * (cmu + 3 * cz) + ℓ ^ 4 + 11 * L * ℓ ^ 2 * cz + L * ℓ ^ 4) * g * c₀ := by
  have hA := mul_le_mul hnu hT hT0 (hnu0.trans hnu)
  have hB := mul_le_mul hyz hlf hlf0 (hyz0.trans hyz)
  have e : ((cmu + 16 / 7 * cz) * g + 16 / 7 * g * s / L ^ 2) * (9 * L ^ 2 * (s * c₀)) +
      (32 / 7 * cz * g + 16 / 7 * g * s) * (18 * L ^ 2 * (s / L * (2 * c₀))) =
      g * c₀ * (9 / 16 * L ^ 2 * ℓ ^ 2 * cmu + 9 / 16 * 16 / 7 * L ^ 2 * ℓ ^ 2 * cz +
        144 / 7 / 256 * ℓ ^ 4 + 1152 / 7 / 16 * L * ℓ ^ 2 * cz + 576 / 7 / 256 * L * ℓ ^ 4) := by
    rw [hs]; field_simp; ring
  have hK : 9 / 16 * L ^ 2 * ℓ ^ 2 * cmu + 9 / 16 * 16 / 7 * L ^ 2 * ℓ ^ 2 * cz +
        144 / 7 / 256 * ℓ ^ 4 + 1152 / 7 / 16 * L * ℓ ^ 2 * cz + 576 / 7 / 256 * L * ℓ ^ 4 ≤
      L ^ 2 * ℓ ^ 2 * (cmu + 3 * cz) + ℓ ^ 4 + 11 * L * ℓ ^ 2 * cz + L * ℓ ^ 4 := by
    have hd : L ^ 2 * ℓ ^ 2 * (cmu + 3 * cz) + ℓ ^ 4 + 11 * L * ℓ ^ 2 * cz + L * ℓ ^ 4 -
        (9 / 16 * L ^ 2 * ℓ ^ 2 * cmu + 9 / 16 * 16 / 7 * L ^ 2 * ℓ ^ 2 * cz +
          144 / 7 / 256 * ℓ ^ 4 + 1152 / 7 / 16 * L * ℓ ^ 2 * cz + 576 / 7 / 256 * L * ℓ ^ 4) =
        7 / 16 * (L ^ 2 * ℓ ^ 2 * cmu) + (3 - 9 / 7) * (L ^ 2 * ℓ ^ 2 * cz) +
          (1 - 144 / 7 / 256) * ℓ ^ 4 + (11 - 1152 / 7 / 16) * (L * ℓ ^ 2 * cz) +
          (1 - 576 / 7 / 256) * (L * ℓ ^ 4) := by ring
    have : 0 ≤ 7 / 16 * (L ^ 2 * ℓ ^ 2 * cmu) + (3 - 9 / 7) * (L ^ 2 * ℓ ^ 2 * cz) +
          (1 - 144 / 7 / 256) * ℓ ^ 4 + (11 - 1152 / 7 / 16) * (L * ℓ ^ 2 * cz) +
          (1 - 576 / 7 / 256) * (L * ℓ ^ 4) := by
      norm_num
      positivity
    linarith
  have hgc : 0 ≤ g * c₀ := mul_nonneg hg hc₀
  calc nu * T + yz * lf ≤ _ := add_le_add hA hB
    _ = _ := e
    _ ≤ g * c₀ * (L ^ 2 * ℓ ^ 2 * (cmu + 3 * cz) + ℓ ^ 4 + 11 * L * ℓ ^ 2 * cz + L * ℓ ^ 4) :=
        mul_le_mul_of_nonneg_left hK hgc
    _ = _ := by ring

/-! ### `k = 0`: the bare covariance -/

section Zero

open DressedFRD

theorem norm_kern_ofR_le {n : ℕ} [NeZero n] (f : Grassmann.Torus 2 n → ℝ) (hf : ∀ m, 0 ≤ f m)
    (x : Grassmann.Torus 2 n) : ‖kern (ofR f) x‖ ≤ ‖kern (ofR f) 0‖ := by
  unfold kern
  rw [norm_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have e0 : ∑ m, ofR f m * FRD.char m 0 = ((∑ m, f m : ℝ) : ℂ) := by
    simp [FRD.char_zero_right, ofR]
  rw [e0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sum_nonneg fun m _ => hf m)]
  refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun m _ => ?_))
  rw [norm_mul, FRD.norm_char, mul_one, ofR, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hf m)]

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (t : Hist.Seq (Xs R))

theorem zh_zero_gb : zh R 0 t = fun _ => 0 := by
  funext i
  show Function.update (rawHist R 0 t).ζ 0 (stZeta R (rawHist R 0 t)) i = 0
  have h0 : stZeta R (rawHist R 0 t) = 0 := by
    simp [stZeta, absorbZeta, clampDisk, rawHist]
  rw [h0]
  rcases eq_or_ne i 0 with rfl | hi
  · simp
  · rw [Function.update_of_ne hi]; rfl

theorem gint_zero_gb (hN : 1 < N) (msq : ℝ) :
    (dData L N msq (fun _ => 0)).Gint 0 = ofR (frdC Pc msq L N 1) := by
  have hZ1 : (dData L N msq (fun _ => 0)).Z 1 = 1 := by simp [Data.Z]
  have hZ0 : (dData L N msq (fun _ => 0)).Z 0 = 1 := by simp [Data.Z]
  have hzp : (dData L N msq (fun _ => 0)).zp 0 = 0 := by simp [Data.zp]
  unfold Data.Gint
  rw [if_pos (by omega), hZ1, hZ0]
  simp [Data.tails, Data.wSc, Data.wLow, hzp, if_pos hN]

/-- **The entries of `C_0` are bounded by its diagonal** (`R.P = Pc`). -/
theorem cov0_entry_le (hP : R.P = Pc) (hN : 1 < N) (hm0 : 0 ≤ R.msq) (x y : Lam 2 L N) :
    ‖Obs2.histCovO R t 0 x y‖ ≤ ‖Obs2.histCovO R t 0 0 0‖ := by
  unfold Obs2.histCovO
  rw [stCov_eq_dData R hP t le_rfl, zh_zero_gb, gint_zero_gb hN]
  simp only [kmat, sub_self]
  exact norm_kern_ofR_le _ (fun m => frdC_nonneg Pc hm0 1 m) _

end Zero

/-! ### Bounds along a history with the bulk context -/

/-- `K_b = L²ℓ⁴(c_μ + 3c_z) + ℓ⁶ + c_zℓ⁴`. -/
def gbKb (L : ℕ) (ℓ cmu cz : ℝ) : ℝ := (L : ℝ) ^ 2 * ℓ ^ 4 * (cmu + 3 * cz) + ℓ ^ 6 + cz * ℓ ^ 4

/-- `K_0 = L²ℓ²(c_μ + 3c_z) + ℓ⁴ + 11Lℓ²c_z + Lℓ⁴`. -/
def gbK0 (L : ℕ) (ℓ cmu cz : ℝ) : ℝ :=
  (L : ℝ) ^ 2 * ℓ ^ 2 * (cmu + 3 * cz) + ℓ ^ 4 + 11 * L * ℓ ^ 2 * cz + L * ℓ ^ 4

/-- `c_e = K_b + K_0`. -/
def gbK (L : ℕ) (ℓ cmu cz : ℝ) : ℝ := gbKb L ℓ cmu cz + gbK0 L ℓ cmu cz

theorem gbKb_nonneg {ℓ cmu cz : ℝ} (hcmu : 0 ≤ cmu) (hcz : 0 ≤ cz) : 0 ≤ gbKb L ℓ cmu cz := by
  unfold gbKb; positivity

theorem gbK0_nonneg {ℓ cmu cz : ℝ} (hcmu : 0 ≤ cmu) (hcz : 0 ≤ cz) : 0 ≤ gbK0 L ℓ cmu cz := by
  unfold gbK0; positivity

theorem gbK_nonneg {ℓ cmu cz : ℝ} (hcmu : 0 ≤ cmu) (hcz : 0 ≤ cz) : 0 ≤ gbK L ℓ cmu cz :=
  add_nonneg (gbKb_nonneg hcmu hcz) (gbK0_nonneg hcmu hcz)

/-- The first line of `Step2.D2.Cprime_values` (the value of `C'_{j+1}(0,0)`) as a named property
of the constants `(ζ̄, K)`. -/
def CpProp (L : ℕ) [NeZero L] (ζbar K : ℝ) : Prop :=
  ∀ (N : ℕ) (msq : ℝ) (ζ : ℕ → ℂ), 1 ≤ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    (∀ i, ‖ζ i‖ ≤ ζbar) → ∀ j, 1 ≤ j → j + 1 < N →
      ‖DressedFRD.kern ((dData L N msq ζ).Z (j + 1) • (dData L N msq ζ).Gint j) 0 -
          (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
        (2 * Real.pi)⁻¹ ^ 2 * (ErrC / ((L : ℝ) ^ j) ^ 2 +
          ErrB * msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2)) +
        K * (dData L N msq ζ).Mz (j + 1)

theorem cpProp_of {L : ℕ} [NeZero L] (hL : 7 ≤ L) : ∃ ζbar K : ℝ, 0 < ζbar ∧ 0 ≤ K ∧ CpProp L ζbar K := by
  obtain ⟨ζbar, hζ, K, hK⟩ := Cprime_values (q := 2) le_rfl hL
  refine ⟨ζbar, max K 0, hζ, le_max_right _ _, fun N msq ζ hN hm0 hm hz j hj hjN => ?_⟩
  have h := (hK (L ^ N) N msq ζ hN rfl hm0 hm hz j hj hjN).1
  have hM := (dData L N msq ζ).Mz_nonneg (j + 1)
  have h2 : K * (dData L N msq ζ).Mz (j + 1) ≤ max K 0 * (dData L N msq ζ).Mz (j + 1) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hM
  exact h.trans (by linarith only [h2])

/-- The threshold `log L ≥ 2π(2 + (2π)^{-2}(ErrC + 2ErrB))` of the lower bound. -/
def gbLog : ℝ := 2 * Real.pi * (2 + (2 * Real.pi)⁻¹ ^ 2 * (ErrC + 2 * ErrB))

namespace C2Ctx

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} {t : Hist.Seq (Xs R)}
  {cmu' cz' cd c : ℝ} (X : C2Ctx R Nh t cmu' cz' cd c)
include X

theorem nuFH_le_gb {k : ℕ} (hk : k ≤ Nh) :
    ‖Obs2.nuFH R t k‖ ≤ zH R t (k + 1) / ((L : ℝ) ^ k) ^ 2 * ((cmu' + 16 / 7 * cz') * (t k).1) := by
  have hL0 := X.L_pos
  set g := (t k).1
  have hg0 : 0 ≤ g := (X.hg k hk).1.le
  set zp := zH R t (k + 1)
  have hzp := X.zpos (k + 1)
  have hmk : R.msq * ((L : ℝ) ^ k) ^ 2 ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ X.hm0) X.hm
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith [X.L7]) (by omega)) 2
  unfold Obs2.nuFH
  refine (norm_sub_le _ _).trans ?_
  have hNu : ‖stNu R k (rawHist R k t) (t k).2.1‖ = |(t k).2.1| * zp / ((L : ℝ) ^ k) ^ 2 := by
    unfold stNu
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_natCast,
      show (L : ℝ) ^ (2 * k) = ((L : ℝ) ^ k) ^ 2 by ring]
    rfl
  have hZr : zH R t k ≤ 8 / 7 * zp := by
    have := zH_ratio_down R X.hρ0 X.hρ8 t (show k ≤ k + 1 by omega)
    rwa [show k + 1 - k = 1 by omega, pow_one] at this
  have hA : ‖stA R (rawHist R k t) * (R.msq : ℂ)‖ ≤ 8 / 7 * zp * ‖zetaH R k t‖ * R.msq := by
    unfold stA
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg X.hm0]
    have e : stZeta R (rawHist R k t) = zetaH R k t := rfl
    rw [e]
    have := norm_nonneg (zetaH R k t)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hZr (norm_nonneg _)) X.hm0
  rw [hNu]
  refine (add_le_add le_rfl hA).trans ?_
  have hμ := X.hμ k hk
  have hζ := X.hζ k hk
  have hLk : 0 < ((L : ℝ) ^ k) ^ 2 := by positivity
  have e1 : 8 / 7 * zp * ‖zetaH R k t‖ * R.msq =
      zp / ((L : ℝ) ^ k) ^ 2 * (8 / 7 * ‖zetaH R k t‖ * (R.msq * ((L : ℝ) ^ k) ^ 2)) := by
    field_simp
  have e2 : |(t k).2.1| * zp / ((L : ℝ) ^ k) ^ 2 = zp / ((L : ℝ) ^ k) ^ 2 * |(t k).2.1| := by ring
  rw [e1, e2, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hm0' : 0 ≤ R.msq * ((L : ℝ) ^ k) ^ 2 := mul_nonneg X.hm0 (by positivity)
  have : 8 / 7 * ‖zetaH R k t‖ * (R.msq * ((L : ℝ) ^ k) ^ 2) ≤ 8 / 7 * (2 * cz' * g) * 1 := by
    have := X.hcz
    gcongr
  have e3 : (cmu' + 16 / 7 * cz') * g = cmu' * g + 8 / 7 * (2 * cz' * g) * 1 := by ring
  rw [e3]
  linarith

theorem gH_le_gb {k : ℕ} (hk : k ≤ Nh) :
    ‖Obs2.gH R t k‖ ≤ 8 / 7 * (t k).1 * zH R t (k + 1) ^ 2 := by
  have e : zH R t (k + 1) = ‖stZ' R (rawHist R k t)‖ := rfl
  unfold Obs2.gH
  rw [norm_mul, norm_pow, ← e]
  exact mul_le_mul_of_nonneg_right (norm_gr_le (X.hg k hk).1.le _ (norm_nCor_le _ _))
    (by positivity)

theorem c0_le_gb {k : ℕ} (hk : k < Nh) :
    ‖Obs2.c0H R t k‖ ≤ R.ℓ ^ 2 / (16 * zH R t (k + 1)) := by
  obtain ⟨hC, -⟩ := X.cov hk
  obtain ⟨hc, hδ, hδ'⟩ := Obs2.histCov_consts R t X.hV hk
  have h := (cov_c0_delta_le hC hc hδ hδ').1
  rwa [ellI_sq] at h

theorem zA_le_gb {k : ℕ} (hk : k ≤ Nh) :
    ‖stA R (rawHist R k t)‖ ≤ 8 / 7 * zH R t (k + 1) * (2 * cz' * (t k).1) := by
  have hZr : zH R t k ≤ 8 / 7 * zH R t (k + 1) := by
    have := zH_ratio_down R X.hρ0 X.hρ8 t (show k ≤ k + 1 by omega)
    rwa [show k + 1 - k = 1 by omega, pow_one] at this
  unfold stA
  rw [norm_mul]
  have e : stZeta R (rawHist R k t) = zetaH R k t := rfl
  rw [e]
  exact mul_le_mul hZr (X.hζ k hk) (norm_nonneg _) (by have := X.zpos (k + 1); positivity)

/-- The bound on `ν'_k`. -/
theorem nu_le_gb {k : ℕ} (hk : k < Nh) :
    ‖(Obs2.kapH R t k).nu‖ ≤
      zH R t (k + 1) * (L : ℝ) ^ 2 / ((L : ℝ) ^ (k + 1)) ^ 2 * ((cmu' + 16 / 7 * cz') * (t k).1) +
        16 / 7 * (t k).1 * zH R t (k + 1) ^ 2 * (R.ℓ ^ 2 / (16 * zH R t (k + 1))) /
          ((L : ℝ) ^ (k + 1)) ^ 2 := by
  have hL0 := X.L_pos
  set g := (t k).1
  have hg0 : 0 ≤ g := (X.hg k hk.le).1.le
  set zp := zH R t (k + 1)
  have hzp := X.zpos (k + 1)
  set s := R.ℓ ^ 2 / (16 * zp) with hs
  set h2 := ((L : ℝ) ^ (k + 1)) ^ 2 with hh2
  have hh2p : 0 < h2 := by positivity
  have hs0 : 0 ≤ s := by positivity
  have hnuF := X.nuFH_le_gb hk.le
  have hgH := X.gH_le_gb hk.le
  have hdl := X.dl_le hk
  rw [Obs2.kapH_nu]
  refine (norm_add_le _ _).trans ?_
  have e1 : zp / ((L : ℝ) ^ k) ^ 2 = zp * (L : ℝ) ^ 2 / h2 := by
    rw [hh2]; field_simp; ring
  rw [e1] at hnuF
  have h4 : ‖4 * Obs2.gH R t k * Obs2.dlH R t k‖ ≤ 4 * (8 / 7 * g * zp ^ 2) * (s / (2 * h2)) := by
    rw [norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hgH (by norm_num)) hdl (norm_nonneg _)
      (by positivity)
  have e2 : 4 * (8 / 7 * g * zp ^ 2) * (s / (2 * h2)) = 16 / 7 * g * zp ^ 2 * s / h2 := by
    field_simp; ring
  linarith

/-- The bound on `y'_k + z'_k`. -/
theorem yz_le_gb {k : ℕ} (hk : k < Nh)
    (hzy : ‖(rawHist R k t).z + (rawHist R k t).y‖ ≤ 2 * cz' * (t k).1 * zH R t k) :
    ‖(rawHist R k t).z + (rawHist R k t).y - stA R (rawHist R k t) -
      Obs2.gH R t k * (Obs2.c0H R t k + Obs2.dlH R t k)‖ ≤
      32 / 7 * cz' * (t k).1 * zH R t (k + 1) +
        16 / 7 * (t k).1 * zH R t (k + 1) ^ 2 * (R.ℓ ^ 2 / (16 * zH R t (k + 1))) := by
  have hL0 := X.L_pos
  set g := (t k).1
  have hg0 : 0 ≤ g := (X.hg k hk.le).1.le
  set zp := zH R t (k + 1)
  have hzp := X.zpos (k + 1)
  set s := R.ℓ ^ 2 / (16 * zp) with hs
  set h2 := ((L : ℝ) ^ (k + 1)) ^ 2 with hh2
  have hh2p : 0 < h2 := by positivity
  have hh21 : 1 ≤ h2 := one_le_pow₀ (one_le_pow₀ (by linarith [X.L7]))
  have hs0 : 0 ≤ s := by positivity
  have hgH := X.gH_le_gb hk.le
  have hdl := X.dl_le hk
  have hc0 := X.c0_le_gb hk
  have hA := X.zA_le_gb hk.le
  have hZr : zH R t k ≤ 8 / 7 * zp := by
    have := zH_ratio_down R X.hρ0 X.hρ8 t (show k ≤ k + 1 by omega)
    rwa [show k + 1 - k = 1 by omega, pow_one] at this
  have hgH0 : 0 ≤ 8 / 7 * g * zp ^ 2 := by positivity
  refine (norm_sub_le _ _).trans ?_
  have h1 := (norm_sub_le ((rawHist R k t).z + (rawHist R k t).y) (stA R (rawHist R k t)))
  have h3 : ‖Obs2.gH R t k * (Obs2.c0H R t k + Obs2.dlH R t k)‖ ≤
      8 / 7 * g * zp ^ 2 * (s + s / (2 * h2)) := by
    rw [norm_mul]
    exact mul_le_mul hgH ((norm_add_le _ _).trans (add_le_add hc0 hdl)) (norm_nonneg _) hgH0
  have h5 : s / (2 * h2) ≤ s := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h6 : 8 / 7 * g * zp ^ 2 * (s + s / (2 * h2)) ≤ 8 / 7 * g * zp ^ 2 * (2 * s) :=
    mul_le_mul_of_nonneg_left (by linarith) hgH0
  have h7 : 2 * cz' * g * zH R t k ≤ 2 * cz' * g * (8 / 7 * zp) :=
    mul_le_mul_of_nonneg_left hZr (by have := X.hcz; positivity)
  have e : 32 / 7 * cz' * g * zp + 16 / 7 * g * zp ^ 2 * s =
      2 * cz' * g * (8 / 7 * zp) + 8 / 7 * zp * (2 * cz' * g) + 8 / 7 * g * zp ^ 2 * (2 * s) := by
    ring
  linarith

/-- **`k ≥ 1`**: `‖E_k(a)‖ ≤ K_bǧ_k/|Z_{k+1}|` (given `|z_k + y_k| ≤ 2c_zǧ_k|Z_k|`). -/
theorem gamBulk_le_pos {k : ℕ} (hk : k < Nh)
    (hzy : ‖(rawHist R k t).z + (rawHist R k t).y‖ ≤ 2 * cz' * (t k).1 * zH R t k)
    (a : Lam 2 L N) :
    ‖ε (FC (Obs2.histCovO R t k) (Obs.LocObs.pbp a) (Vcoup (Obs2.kapH R t k) univ))‖ ≤
      gbKb L R.ℓ cmu' cz' * (t k).1 / zH R t (k + 1) := by
  have hL0 := X.L_pos
  have hg0 : 0 ≤ (t k).1 := (X.hg k hk.le).1.le
  have hzp := X.zpos (k + 1)
  rw [eps_hist_eq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  obtain ⟨hC, -⟩ := X.cov hk
  have hT := Obs2.norm_sumCC_le hC (X.iN hk) a
  have hlf := Obs2.norm_lfunC_le hC (X.iN hk) a
  rw [ellI_sq] at hT
  rw [show (fscale (stZ' R (rawHist R k t)) * R.ℓ / 4) ^ 4 =
    (fscale (stZ' R (rawHist R k t)) * R.ℓ / 4) ^ 2 * (fscale (stZ' R (rawHist R k t)) * R.ℓ / 4) ^ 2
    by ring, ellI_sq] at hlf
  have hb := gb_alg_pos (nu := ‖(Obs2.kapH R t k).nu‖)
    (T := ‖∑ x, Obs2.histCovO R t k a x * Obs2.histCovO R t k x a‖)
    (lf := ‖Obs2.lfunC (Obs2.histCovO R t k) a‖) (ℓ := R.ℓ) hzp hg0 (by positivity)
    (by positivity) X.hcmu X.hcz rfl (X.nu_le_gb hk) hT (X.yz_le_gb hk hzy) hlf (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  exact hb.trans_eq (by unfold gbKb; ring)

/-- **`k = 0`**: `‖E_0(a)‖ ≤ K_0ǧ_0‖C_0(0,0)‖` (bare covariance with a nonnegative symbol). -/
theorem gamBulk_le_zero (hP : R.P = Pc) (h0 : 0 < Nh)
    (hzy : ‖(rawHist R 0 t).z + (rawHist R 0 t).y‖ ≤ 2 * cz' * (t 0).1 * zH R t 0)
    (a : Lam 2 L N) :
    ‖ε (FC (Obs2.histCovO R t 0) (Obs.LocObs.pbp a) (Vcoup (Obs2.kapH R t 0) univ))‖ ≤
      gbK0 L R.ℓ cmu' cz' * (t 0).1 * ‖Obs2.histCovO R t 0 0 0‖ := by
  have hL0 := X.L_pos
  have hg0 : 0 ≤ (t 0).1 := (X.hg 0 h0.le).1.le
  have hz1 : zH R t (0 + 1) = 1 := by
    show ‖(rawHist R 1 t).Z‖ = 1
    rw [rawHist_one_Z, norm_one]
  have hN1 : 1 < N := by have := X.hN; omega
  have hc := cov0_entry_le R t hP hN1 X.hm0
  rw [eps_hist_eq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  obtain ⟨hC, -⟩ := X.cov h0
  have hT := Obs2.norm_sumCC_le_c0 hC (X.iN h0) hc a
  have hlf := Obs2.norm_lfunC_le_c0 hC (X.iN h0) hc a
  rw [ellI_sq, hz1, zero_add, pow_one] at hT hlf
  have hnu := X.nu_le_gb h0
  have hyz := X.yz_le_gb h0 hzy
  rw [hz1] at hnu hyz
  simp only [zero_add, pow_one, one_pow, mul_one, one_mul] at hnu hyz hT hlf
  have hb := gb_alg_zero (nu := ‖(Obs2.kapH R t 0).nu‖)
    (T := ‖∑ x, Obs2.histCovO R t 0 a x * Obs2.histCovO R t 0 x a‖)
    (lf := ‖Obs2.lfunC (Obs2.histCovO R t 0) a‖) (ℓ := R.ℓ) (s := R.ℓ ^ 2 / 16)
    (c₀ := ‖Obs2.histCovO R t 0 0 0‖) hg0 hL0
    X.hcmu X.hcz (norm_nonneg _) rfl (hnu.trans (le_of_eq (by field_simp))) hT hyz hlf
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  exact hb.trans_eq (by unfold gbK0; ring)

/-- **The lower bound `|Z_{k+1}Γ^{int}_{k+1}(0,0)| ≥ 1`** for `1 ≤ k < N_h`. -/
theorem gamInt_lower (hm0 : 0 < R.msq)
    (hmN : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) {ζbar K εb : ℝ} (hCp : CpProp L ζbar K)
    (hK0 : 0 ≤ K) (hζ : 2 * c * εb ≤ ζbar) (hKε : K * (2 * c * εb) ≤ 1)
    (hgε : ∀ j ≤ Nh, (t j).1 ≤ εb) (hlog : gbLog ≤ Real.log L) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k < Nh) : 1 ≤ zH R t (k + 1) * ‖GamInt R k t‖ := by
  have hL0 := X.L_pos
  have hc0 := X.c_nonneg
  have hg0 : 0 ≤ (t k).1 := (X.hg k hk.le).1.le
  have hzb : ∀ i, ‖zh R k t i‖ ≤ 2 * c * εb := fun i => by
    refine (X.zh_le hk i).trans ?_
    have := X.hcz1; have := X.hcz; have := hgε k hk.le
    gcongr
  have hN1 : 1 ≤ N := by have := X.hN; omega
  have hkN : k + 1 < N := X.iN hk
  have h := hCp N R.msq (zh R k t) hN1 hm0 hmN (fun i => (hzb i).trans hζ) k hk1 hkN
  have hV : ∀ i ≤ k, ValidAt R i := fun i hi => X.hV i (by omega)
  rw [← Z_mul_gamInt R hV t] at h
  have hMz : (dData L N R.msq (zh R k t)).Mz (k + 1) ≤ 2 * c * εb :=
    DressedFRD.Data.Mz_le (D := dData L N R.msq (zh R k t))
      (mul_nonneg (mul_nonneg two_pos.le hc0) (hg0.trans (hgε k hk.le)))
      fun i _ => hzb i
  have hKM : K * (dData L N R.msq (zh R k t)).Mz (k + 1) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hMz hK0).trans hKε
  have hLk : 1 ≤ ((L : ℝ) ^ k) ^ 2 := one_le_pow₀ (one_le_pow₀ (by linarith [X.L7]))
  have hm1 : R.msq * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ X.hm0) X.hm
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith [X.L7]) (by omega)) 2
  have hm2 : R.msq * ((L : ℝ) ^ k) ^ 2 ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ X.hm0) X.hm
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith [X.L7]) (by omega)) 2
  have hEC := ErrC_nonneg'
  have hEB := ErrB_nonneg
  have hp : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ ^ 2 := by positivity
  have hE1 : ErrC / ((L : ℝ) ^ k) ^ 2 ≤ ErrC := div_le_self hEC hLk
  have hE2 : ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2) ≤ 2 * ErrB := by
    have e : ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2) =
        ErrB * (R.msq * ((L : ℝ) ^ k) ^ 2 + R.msq * ((L : ℝ) ^ (k + 1)) ^ 2) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left (show R.msq * ((L : ℝ) ^ k) ^ 2 +
      R.msq * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 2 by linarith) hEB
    linarith
  have hB : (2 * Real.pi)⁻¹ ^ 2 * (ErrC / ((L : ℝ) ^ k) ^ 2 +
      ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2)) ≤
      (2 * Real.pi)⁻¹ ^ 2 * (ErrC + 2 * ErrB) :=
    mul_le_mul_of_nonneg_left (by linarith) hp
  have hlam : 2 + (2 * Real.pi)⁻¹ ^ 2 * (ErrC + 2 * ErrB) ≤ Real.log L / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    unfold gbLog at hlog; linarith
  have hrev := norm_sub_norm_le (((Real.log L / (2 * Real.pi) : ℝ)) : ℂ)
    ((rawHist R (k + 1) t).Z * GamInt R k t)
  rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_trans (by positivity) hlam : (0 : ℝ) ≤ Real.log L / (2 * Real.pi))]
    at hrev
  have e : zH R t (k + 1) * ‖GamInt R k t‖ = ‖(rawHist R (k + 1) t).Z * GamInt R k t‖ := by
    rw [norm_mul]
  rw [e]
  linarith

theorem cov00_eq_gamInt (hP : R.P = Pc) (k : ℕ) : Obs2.histCovO R t k 0 0 = GamInt R k t := by
  unfold Obs2.histCovO GamInt
  rw [stCov_eq_dData R hP t le_rfl]
  simp [DressedFRD.kmat]

/-- **`GamBulkRel` at every point along a history with the bulk context.** -/
theorem gamBulk_rel_ctx (hP : R.P = Pc) (hm0 : 0 < R.msq)
    (hmN : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) {ζbar K εb : ℝ} (hCp : CpProp L ζbar K)
    (hK0 : 0 ≤ K) (hζ : 2 * c * εb ≤ ζbar) (hKε : K * (2 * c * εb) ≤ 1)
    (hgε : ∀ j ≤ Nh, (t j).1 ≤ εb) (hlog : gbLog ≤ Real.log L)
    (hzy : ∀ k < Nh, ‖(rawHist R k t).z + (rawHist R k t).y‖ ≤ 2 * cz' * (t k).1 * zH R t k)
    (a : Lam 2 L N) {k : ℕ} (hk : k < Nh) :
    ‖ε (FC (Obs2.histCovO R t k) (Obs.LocObs.pbp a) (Vcoup (Obs2.kapH R t k) univ))‖ ≤
      gbK L R.ℓ cmu' cz' * ((t k).1 + zA L R.msq k) * ‖GamInt R k t‖ := by
  have hg0 : 0 ≤ (t k).1 := (X.hg k hk.le).1.le
  have ha0 : 0 ≤ zA L R.msq k := zA_nonneg L X.hm0 k
  have hKb := gbKb_nonneg (L := L) (ℓ := R.ℓ) X.hcmu X.hcz
  have hK0' := gbK0_nonneg (L := L) (ℓ := R.ℓ) X.hcmu X.hcz
  have hΓ := norm_nonneg (GamInt R k t)
  have hmono : ∀ K' : ℝ, 0 ≤ K' → K' ≤ gbK L R.ℓ cmu' cz' →
      K' * (t k).1 * ‖GamInt R k t‖ ≤ gbK L R.ℓ cmu' cz' * ((t k).1 + zA L R.msq k) *
        ‖GamInt R k t‖ := fun K' h0 h1 =>
    mul_le_mul_of_nonneg_right (mul_le_mul h1 (by linarith) hg0 (gbK_nonneg X.hcmu X.hcz)) hΓ
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have h := X.gamBulk_le_zero hP hk (hzy 0 hk) a
    rw [cov00_eq_gamInt X hP] at h
    exact h.trans (hmono _ hK0' (by unfold gbK; linarith))
  · have h := X.gamBulk_le_pos hk (hzy k hk) a
    have hlo := X.gamInt_lower hm0 hmN hCp hK0 hζ hKε hgε hlog hk1 hk
    have hzp := X.zpos (k + 1)
    have h2 : gbKb L R.ℓ cmu' cz' * (t k).1 / zH R t (k + 1) ≤
        gbKb L R.ℓ cmu' cz' * (t k).1 * ‖GamInt R k t‖ := by
      rw [div_le_iff₀ hzp]
      have := mul_le_mul_of_nonneg_left hlo (mul_nonneg hKb hg0)
      linarith
    exact h.trans (h2.trans (hmono _ hKb (by unfold gbK; linarith)))

end C2Ctx


/-! ### Under the master constants -/

/-- The requirement on `ε` (`c = c_R`): the constants `(ζ̄, K)` of `CpProp`, `2cε ≤ ζ̄`,
`K·2cε ≤ 1` (`c = ceff`) and `βε ≤ 1/2`. -/
def gbEReq (L : ℕ) (_A c _c' ε : ℝ) : Prop :=
  ∀ [NeZero L], 7 ≤ L → ∃ ζbar K : ℝ, 0 < ζbar ∧ 0 ≤ K ∧ CpProp L ζbar K ∧
    2 * ceff L c * ε ≤ ζbar ∧ K * (2 * ceff L c * ε) ≤ 1 ∧ betaL L * ε ≤ 1 / 2

theorem gbEReq_ev (L : ℕ) (A c c' : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), gbEReq L A c c' ε := by
  by_cases hL : L ≠ 0 ∧ 7 ≤ L
  · haveI : NeZero L := ⟨hL.1⟩
    obtain ⟨ζbar, K, hζ, hK, hCp⟩ := cpProp_of (L := L) hL.2
    filter_upwards [ev_lin (2 * ceff L c) hζ, ev_lin (K * (2 * ceff L c)) one_pos,
      ev_lin (betaL L) (by norm_num : (0 : ℝ) < 1 / 2)] with ε h1 h2 h3
    intro _ _
    exact ⟨ζbar, K, hζ, hK, hCp, h1, by rw [← mul_assoc]; exact h2, h3⟩
  · exact Eventually.of_forall fun _ inst hL7 => absurd ⟨inst.out, hL7⟩ hL

/-- `GamBulkRelA` along every admissible trajectory (`N_h = N - 2`) with one constant `c_e`. -/
def GamBulkConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε ce : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    GamBulkRelA R Nh m b μ₀ ce

/-- `ℓ ↦ L` threshold: `L ≥ 49` and `log L ≥ gbLog`. -/
def gbL0 : ℕ := max 49 ⌈Real.exp gbLog⌉₊

theorem log_ge_gbLog {L : ℕ} (hL : gbL0 ≤ L) : gbLog ≤ Real.log L := by
  have hc : ⌈Real.exp gbLog⌉₊ ≤ L := le_trans (le_max_right _ _) hL
  have h1 : Real.exp gbLog ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast hc)
  have h0 : 0 < Real.exp gbLog := Real.exp_pos _
  calc gbLog = Real.log (Real.exp gbLog) := (Real.log_exp _).symm
    _ ≤ Real.log L := Real.log_le_log h0 h1

set_option maxHeartbeats 4000000 in
/-- **`GamBulkRel` discharged** (at every point): one set of constants with `FlowC2Concl`,
`ε ≤ 1`, `SpinConcl`, `MagConcl` and `GamBulkConcl` with `c_e = gbK L ℓ c_μ (16ℓ²/49)`. -/
theorem thm_gam_bulk : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG ce : ℝ,
      FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ ε ≤ 1 ∧
      SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧ MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧
      0 ≤ ce ∧ GamBulkConcl L ℓ A ρ κ cm cT ε ce := by
  obtain ⟨L₀, hL₀⟩ := thm_flow_master_all (fun _ _ => True) (fun _ => ⟨0, fun _ _ => trivial⟩)
    gbEReq gbEReq_ev
  refine ⟨max L₀ gbL0, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, -, -, hSp, hMag, -, -, -,
    C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx, hXm⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  have hLg : gbL0 ≤ L := le_trans (le_max_right _ _) hL
  have hL49 : 49 ≤ L := le_trans (le_max_left _ _) hLg
  have hlog := log_ge_gbLog hLg
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id hC2
  let R₀ : RGPar 2 L 1 := ⟨Pc, 0, ℓ, A, 0, ρ⟩
  obtain ⟨ζbar, K, -, hK, hCp, hζε, hKε, hβε⟩ := hEx R₀ rfl (by omega)
  set c := cR R₀ ((L : ℝ) ^ 2) cm C₂x with hc
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG,
    gbK L ℓ (max (cmu ((L : ℝ) ^ 2) cm) 0) (16 * ℓ ^ 2 / 49), hC2, hε1, hSp, hMag, ?_, ?_⟩
  · exact gbK_nonneg (le_max_right _ _) (by positivity)
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm a k hk
  set R' := R.withMsq m with hR'
  obtain ⟨H, hm1, F1⟩ := hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  obtain ⟨hV, hVL⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have ht := admissible_InDh_rg R' F1 hadm Nh le_rfl
  have hRA' : R'.A = A := hRA
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = ρ from hRρ]; exact hρpos.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = ρ from hRρ]; exact hρ8
  have hcR : cR R' ((L : ℝ) ^ 2) cm C₂x = c := cR_congr (show R.ℓ = ℓ from hRℓ) _ _ _
  have hSB' : StepBounds L R'.A C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx := by rw [hRA']; exact hSBx
  have hmsq : R'.msq ∈ mRange L N := hm
  have hβ0 : 0 ≤ betaL L := by have := betaL_ge (by omega : 8 ≤ L); linarith
  have X := c2ctx_master R' hNh hL49 hSB' H hm1 hV hVL hρ0' hρ8' hmsq hβε ht
  rw [hcR] at X
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have hgε : ∀ j ≤ Nh, (t j).1 ≤ ε := fun j hj => (ht.1 j hj).2.1
  have hDh : ∀ j ≤ Nh, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t := fun j hj =>
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  have hzy : ∀ j < Nh, ‖(rawHist R' j t).z + (rawHist R' j t).y‖ ≤
      2 * cZ R' * (t j).1 * zH R' t j := by
    intro j hj
    obtain ⟨hz, hy, -⟩ := apriori R' hSB' hV hm1 hβ0 (by norm_num) H j hj.le t (hDh j hj.le)
    have hZ := zH_pos R' hρ0' hρ8' t j
    have hZne : (rawHist R' j t).Z ≠ 0 := norm_pos_iff.1 hZ
    have e : (rawHist R' j t).z + (rawHist R' j t).y =
        (rawHist R' j t).Z * ((rawHist R' j t).z / (rawHist R' j t).Z +
          (rawHist R' j t).y / (rawHist R' j t).Z) := by field_simp
    rw [e, norm_mul]
    have := (norm_add_le _ _).trans (add_le_add hz hy)
    have e2 : 2 * cZ R' * (t j).1 * zH R' t j = zH R' t j * (cZ R' * (t j).1 + cZ R' * (t j).1) := by
      ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left this hZ.le
  have h := X.gamBulk_rel_ctx hP hm.1 hm.2 hCp hK hζε hKε hgε hlog hzy a hk
  have hℓ' : R'.ℓ = ℓ := hRℓ
  have hcZ : cZ R' = 16 * ℓ ^ 2 / 49 := by unfold cZ; rw [hℓ']
  have hle : gbK L R'.ℓ (cmu ((L : ℝ) ^ 2) cm) (cZ R') ≤
      gbK L ℓ (max (cmu ((L : ℝ) ^ 2) cm) 0) (16 * ℓ ^ 2 / 49) := by
    rw [hcZ, hℓ']
    unfold gbK gbKb gbK0
    have h1 := le_max_left (cmu ((L : ℝ) ^ 2) cm) 0
    have h2 : 0 ≤ (L : ℝ) ^ 2 * ℓ ^ 4 := by positivity
    have h3 : 0 ≤ (L : ℝ) ^ 2 * ℓ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left h1 h2
    have := mul_le_mul_of_nonneg_left h1 h3
    nlinarith
  have hga : 0 ≤ (t k).1 + zA L m k :=
    add_nonneg (X.hg k hk.le).1.le (zA_nonneg L hm.1.le k)
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hga) (norm_nonneg _))


end

end Spin2
