import Spin2.Case2.Case2Bd
import PtCorr2.Zero.ExactHist

/-!
# `Case2Bulk` (ii): the second-order `ν` flow

* **`nu_sharp`** (one raw step, from `Step2.rawStep_coup`): the `ν`-coordinate of the output couplings
  is `ν♭ + 4gδ` (the first-order shift `ν'`) up to `κ_Q` (bounded by `‖K♭‖`) and `κ_L` (bounded by
  `v² + w`):
  `|κ_ν - (ν♭ + 4gZ'²δ)| ≤ C_q s^{-2}R_Q/L^{2j} + 4C_q s^{-4}R_Q|δ| + C_q s'^{-2}R_L/L^{2(j+1)}`,
  with the inputs of `StepBounds` (`R_Q = c_S C_l 8k`, `R_L = C_l L² σ(v, w)`);
* `C2Ctx.S_le`: `|S_{k+1}| ≤ (27/16)ℓ²L^{2(k+1)}/|Z_{k+1}|`;
* **`nuflow_le`** (along a real admissible trajectory): `|(ν♭_{k+1} - ν'_k)S_{k+1}| ≤ B₂(ǧ_k² + ǧ_kzA_k)`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- The sharp `ν`-step property with constants `C_q, C_l, c_S` (at fixed `L`). -/
def NuSharp (L : ℕ) [NeZero L] (Cq Cl cS : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidAt R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
      ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
        8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
      ∀ A wl dd k r : ℝ, 2 ≤ A → 0 ≤ wl → 0 ≤ dd → 0 ≤ k →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal k →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 → r ≤ 1 →
      8 * k ≤ 1 →
      ‖stCv R j st g μ D K 2 - (stNu R j st μ - stA R st * R.msq +
          4 * (stGr R j st g μ * stZ' R st ^ 2) *
            (stCov R j st (dirVec (Sum.inl 0)) 0 - stCov R j st 0 0))‖ ≤
        Cq * ((fscale st.Z * R.ℓ) ^ 2)⁻¹ * (cS * (Cl * (8 * k))) / ((L : ℝ) ^ j) ^ 2 +
        4 * (Cq * ((fscale st.Z * R.ℓ) ^ 4)⁻¹ * (cS * (Cl * (8 * k)))) *
          ‖stCov R j st (dirVec (Sum.inl 0)) 0 - stCov R j st 0 0‖ +
        Cq * ((fscale (stZ' R st) * R.ℓ) ^ 2)⁻¹ *
          (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g)
            (wl + dd))) / ((L : ℝ) ^ (j + 1)) ^ 2

set_option maxHeartbeats 4000000 in
/-- **The sharp `ν`-coordinate after one raw step.** -/
theorem nu_sharp : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L → NuSharp L Cq Cl cS := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hcoup⟩ := rawStep_coup
  refine ⟨Cq, hCq, Cl, hCl, cS, hcS, ?_⟩
  intro L _ hL8 hLp N R j hV st H g μ D K hD hK hm hg0 η hz hy hη hηs A wl dd k r hA2 hwl0 hdd0
    hk0 hWl hDd hKk hvr hwr hr1 hk8
  set v := cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g with hvdef
  set δ := stCov R j st (dirVec (Sum.inl 0)) 0 - stCov R j st 0 0 with hδdef
  have hV' := hV
  obtain ⟨hj2, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hz
  have hjN : j < N := by omega
  -- clamps
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hyc : ‖st.y / st.Z‖ ≤ R.ρ := by linarith
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζη : ‖stZeta R st‖ ≤ 2 * η := by
    rw [hζ, add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := by linarith
  have hs := fscale_pos hZ
  have hsℓ : 0 < fscale st.Z * R.ℓ := mul_pos hs hℓ
  -- the inputs
  have hrZ : ‖stZ' R st / st.Z‖ ≤ 9 / 8 := by
    have e : stZ' R st / st.Z = 1 + stZeta R st := by
      unfold stZ'; rw [mul_div_cancel_left₀ _ hZ]
    rw [e]; refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
  have hVv : Fnorm j (fscale st.Z * R.ℓ) (stVf R j st g μ) ≤ ENNReal.ofReal v := by
    have e : stVf R j st g μ = VfamL j ![0, 0, (μ : ℂ) * stZ' R st / (L : ℂ) ^ (2 * j) -
        stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2] := stVf_eq hZ hzy hyc
    rw [e]
    refine (Fnorm_VfamL_norm2 j hjN.le hℓ hZ _ 0 0 _ _ μ R.msq).trans
      (ENNReal.ofReal_le_ofReal ?_)
    simp only [zero_div, norm_zero, add_zero]
    rw [norm_stA_div hZ]
    have : ‖stZeta R st‖ * |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 2 * η := by
      rw [mul_assoc]
      calc ‖stZeta R st‖ * (|R.msq| * ((L : ℝ) ^ j) ^ 2) ≤ 2 * η * 1 := by gcongr
        _ = 2 * η := mul_one _
    have h1 : ‖stZ' R st / st.Z‖ * |μ| ≤ 2 * |μ| := by
      have := mul_le_mul_of_nonneg_right hrZ (abs_nonneg μ); linarith [abs_nonneg μ]
    have hgr := norm_stGr_le R j st g μ
    rw [abs_of_nonneg hg0] at hgr
    have h2 : ‖stZ' R st / st.Z‖ ^ 2 * ‖stGr R j st g μ‖ ≤ 2 * g := by
      have hr2 : ‖stZ' R st / st.Z‖ ^ 2 ≤ 81 / 64 := by
        have := norm_nonneg (stZ' R st / st.Z); nlinarith
      calc ‖stZ' R st / st.Z‖ ^ 2 * ‖stGr R j st g μ‖ ≤ 81 / 64 * (8 / 7 * g) := by
            gcongr
        _ ≤ 2 * g := by linarith
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have hℓ4 : 0 ≤ R.ℓ ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_left (add_le_add h1 this) (mul_nonneg hM (sq_nonneg R.ℓ))
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * R.ℓ ^ 4)
    rw [hvdef]
    nlinarith
  have hw : Fnorm j (fscale st.Z * R.ℓ) (st.Wl + D) ≤ ENNReal.ofReal (wl + dd) :=
    Fnorm_add_le _ _ hwl0 hdd0 hWl hDd
  have hv0 : 0 ≤ v := by rw [hvdef]; positivity
  have hv1 : v ≤ 1 := hvr.trans hr1
  have hr0 : 0 ≤ r := hv0.trans hvr
  have hw1 : wl + dd ≤ 1 := hwr.trans (by nlinarith)
  -- `Δ` and `K♭`
  set δΔ := 8 * cM * R.ℓ ^ 2 * η with hδΔ
  have hδΔ0 : 0 ≤ δΔ := by have := (Nat.cast_nonneg (α := ℝ) (Fintype.card (Mono 2))); positivity
  have hΔ : Fnorm j (fscale st.Z * R.ℓ) (stDelta R j st) ≤ ENNReal.ofReal δΔ := by
    refine (Fnorm_stDelta_le hjN.le hℓ hZ (2 * η) hζη
      (by rw [stYc_eq hZ hyc]; linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 2 * η * |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 2 * η := by
      rw [mul_assoc]
      calc 2 * η * (|R.msq| * ((L : ℝ) ^ j) ^ 2) ≤ 2 * η * 1 := by gcongr
        _ = 2 * η := mul_one _
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    rw [hδΔ]
    nlinarith [mul_nonneg hM (sq_nonneg R.ℓ)]
  have hKf := Knorm_stKflat_le (R := R) j hsℓ (by linarith : (0 : ℝ) ≤ A) hδΔ0 st hΔ K
  have hexp : Real.exp (4 * δΔ) ≤ 8 := by
    have : 4 * δΔ ≤ 2 := by linarith
    calc Real.exp (4 * δΔ) ≤ Real.exp 2 := Real.exp_le_exp.2 this
      _ ≤ 8 := by
          have := Real.exp_one_lt_d9
          have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          nlinarith [Real.exp_pos 1]
  have hKflat : Knorm j (fscale st.Z * R.ℓ) (A / 2) (Kflat j (stDelta R j st) K) ≤
      ENNReal.ofReal (8 * k) := by
    have hmono : A / 2 ≤ A * Real.exp (-δΔ) := by
      have : (1 : ℝ) / 2 ≤ Real.exp (-δΔ) := by
        have h1 := Real.add_one_le_exp (-δΔ)
        linarith
      nlinarith
    refine (Knorm_mono_A (by linarith) hmono _).trans (hKf.trans ?_)
    rw [ENNReal.ofReal_mul (by norm_num)]
    calc ENNReal.ofReal (Real.exp (4 * δΔ)) * Knorm j (fscale st.Z * R.ℓ) A K
        ≤ ENNReal.ofReal 8 * ENNReal.ofReal k := by
          gcongr
      _ = _ := rfl
  -- the couplings
  obtain ⟨c₀, δ', κQ, κL, hc₀, hδ, hrep, -, -, q3, q4, -, -, l3, -, -⟩ :=
    hcoup L hL8 hLp N R j hV st H g μ D K hD hK (A / 2) (by linarith) v (wl + dd) (8 * k)
      hv0 (by positivity) (by positivity) hv1 hw1 hk8 hVv hw hKflat
  have hδe : δ = δ' := by
    have h1 := hδ 0 (Sum.inl 0)
    rw [zero_add] at h1
    show stCov R j st (dirVec (Sum.inl 0)) 0 - stCov R j st 0 0 = δ'
    rw [h1, hc₀ 0]; ring
  have en : stCv R j st g μ D K 2 = (stNu R j st μ - stA R st * R.msq +
      2 * (2 : ℕ) * (stGr R j st g μ * stZ' R st ^ 2) * δ') -
      (κQ.nu + 2 * (2 : ℕ) * κQ.g * δ') - κL.nu := congrArg Coup.nu hrep
  rw [en, hδe]
  have e : (stNu R j st μ - stA R st * R.msq + 2 * ((2 : ℕ) : ℂ) * (stGr R j st g μ * stZ' R st ^ 2) * δ') -
      (κQ.nu + 2 * ((2 : ℕ) : ℂ) * κQ.g * δ') - κL.nu -
      (stNu R j st μ - stA R st * R.msq + 4 * (stGr R j st g μ * stZ' R st ^ 2) * δ') =
      -(κQ.nu + 4 * κQ.g * δ' + κL.nu) := by push_cast; ring
  rw [e, norm_neg]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add q3 ?_)) l3)
  rw [norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left q4 (by norm_num)) (norm_nonneg _)

namespace C2Ctx

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} {t : Hist.Seq (Xs R)}
  {cmu' cz' cd c : ℝ} (X : C2Ctx R Nh t cmu' cz' cd c)
include X

/-- `|S_{k+1}| ≤ (27/16)ℓ²L^{2(k+1)}/|Z_{k+1}|`. -/
theorem S_le {k : ℕ} (hk : k < Nh) (a : Lam 2 L N) :
    ‖∑ i ∈ range (k + 1), Obs2.rowS (Obs2.histCovO R t i) a‖ ≤
      27 / 16 * R.ℓ ^ 2 * ((L : ℝ) ^ (k + 1)) ^ 2 / zH R t (k + 1) := by
  have hL0 := X.L_pos
  have hL7 := X.L7
  have hzk := X.zpos (k + 1)
  set y := 8 / 7 * ((L : ℝ) ^ 2)⁻¹ with hy
  have hy0 : 0 ≤ y := by positivity
  have hy3 : y ≤ 1 / 3 := by
    rw [hy, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith
  set K1 := 9 / 8 * R.ℓ ^ 2 * ((L : ℝ) ^ (k + 1)) ^ 2 / zH R t (k + 1) with hK1
  have hK10 : 0 ≤ K1 := by positivity
  refine (norm_sum_le _ _).trans ?_
  refine (sum_le_sum fun i hi => ?_).trans ((mul_sum _ _ _).symm.le.trans
    ((mul_le_mul_of_nonneg_left (Obs2.geom_tail_le' hy0 hy3 k) hK10).trans (le_of_eq ?_)))
  · have hi' := mem_range.1 hi
    have hzi := X.zpos (i + 1)
    refine (X.rowS_le (show i < Nh by omega) a).trans ?_
    have hr := pow_ratio_L2 hL0 (show i ≤ k by omega)
    have hzr := zH_ratio_up R X.hρ0 X.hρ8 t (show i + 1 ≤ k + 1 by omega)
    rw [show k + 1 - (i + 1) = k - i by omega] at hzr
    have e : 18 * ((L : ℝ) ^ (i + 1)) ^ 2 * (R.ℓ ^ 2 / (16 * zH R t (i + 1))) =
        K1 * (zH R t (k + 1) / zH R t (i + 1)) *
          (((L : ℝ) ^ (i + 1)) ^ 2 / ((L : ℝ) ^ (k + 1)) ^ 2) := by
      rw [hK1]; field_simp; ring
    rw [e, hr]
    have hzz : zH R t (k + 1) / zH R t (i + 1) ≤ (8 / 7 : ℝ) ^ (k - i) := by
      rw [div_le_iff₀ hzi]; exact hzr
    have e2 : K1 * y ^ (k - i) = K1 * (8 / 7 : ℝ) ^ (k - i) * (((L : ℝ) ^ 2)⁻¹) ^ (k - i) := by
      rw [hy, mul_pow]; ring
    rw [e2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzz hK10) (by positivity)
  · rw [hK1]; ring

end C2Ctx

/-- The constant `B₂` of `Case2Bulk` (ii). -/
def nuB (L : ℕ) (Cq Cl cS cxv cRv c : ℝ) : ℝ :=
  16 * (L : ℝ) ^ 2 * Cq * cS * Cl * cxv +
    2 * Cq * Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cRv ^ 2 + 7 * c

theorem mP_le_zA {L : ℕ} {m : ℝ} (hm0 : 0 ≤ m) (hL : (1 : ℝ) ≤ L) {k : ℕ}
    (h0 : m * (L : ℝ) ^ 2 ≤ 1) : m * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ zA L m k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [zA_zero]; simpa using h0
  · rw [zA_pos L m hk]
    have : 0 ≤ (((L : ℝ) ^ k) ^ 2)⁻¹ := by positivity
    linarith

/-- The pure algebra of `nuflow_le`. -/
theorem nuflow_alg {Cq RQ RL a a' ℓ Pk L2 Sb dl : ℝ} (hCq : 0 ≤ Cq) (hRQ : 0 ≤ RQ) (hRL : 0 ≤ RL)
    (ha : 0 < a) (ha' : 0 < a') (hℓ : 0 < ℓ) (hPk : 0 < Pk) (hL2 : 0 < L2)
    (hdl : dl ≤ ℓ ^ 2 / (16 * a') / (2 * (Pk * L2))) (hdl0 : 0 ≤ dl)
    (hSb : Sb = 27 / 16 * ℓ ^ 2 * (Pk * L2) / a') :
    (Cq * ((ℓ ^ 2 / a))⁻¹ * RQ / Pk + 4 * (Cq * ((ℓ ^ 2 / a) ^ 2)⁻¹ * RQ) * dl +
        Cq * (ℓ ^ 2 / a')⁻¹ * RL / (Pk * L2)) * Sb ≤
      27 / 16 * Cq * RQ * L2 * (a / a') + 27 / 128 * Cq * RQ * (a / a') ^ 2 + 27 / 16 * Cq * RL := by
  have hS0 : 0 ≤ Sb := by rw [hSb]; positivity
  have h1 : 4 * (Cq * ((ℓ ^ 2 / a) ^ 2)⁻¹ * RQ) * dl ≤
      4 * (Cq * ((ℓ ^ 2 / a) ^ 2)⁻¹ * RQ) * (ℓ ^ 2 / (16 * a') / (2 * (Pk * L2))) :=
    mul_le_mul_of_nonneg_left hdl (by positivity)
  have h2 : (Cq * ((ℓ ^ 2 / a))⁻¹ * RQ / Pk + 4 * (Cq * ((ℓ ^ 2 / a) ^ 2)⁻¹ * RQ) * dl +
        Cq * (ℓ ^ 2 / a')⁻¹ * RL / (Pk * L2)) * Sb ≤
      (Cq * ((ℓ ^ 2 / a))⁻¹ * RQ / Pk +
        4 * (Cq * ((ℓ ^ 2 / a) ^ 2)⁻¹ * RQ) * (ℓ ^ 2 / (16 * a') / (2 * (Pk * L2))) +
        Cq * (ℓ ^ 2 / a')⁻¹ * RL / (Pk * L2)) * Sb :=
    mul_le_mul_of_nonneg_right (by linarith) hS0
  refine h2.trans (le_of_eq ?_)
  rw [hSb]
  field_simp
  ring

namespace C2Ctx

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} {cmu' cz' cd c : ℝ}

set_option maxHeartbeats 4000000 in
/-- **`Case2Bulk` (ii)**: the second-order `ν` flow along a real trajectory. -/
theorem nuflow_le {b μ₀ : ℝ}
    (X : C2Ctx R Nh (Hist.traj (rgData R) ((L : ℝ) ^ 2) b μ₀) cmu' cz' cd c)
    {Cq Cl cS : ℝ} (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl) (hcS : 1 ≤ cS) (hNu : NuSharp L Cq Cl cS)
    {C₀ η εs CK C₂ CD Cq0 Cl0 cS0 : ℝ} (hSB : StepBounds L R.A C₀ η εs CK C₂ CD Cq0 Cl0 cS0)
    {β δ κ cg cm cT ε : ℝ} (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) (hβ : 0 ≤ β)
    (hδ1 : δ ≤ 1) (H : ApHyp R ((L : ℝ) ^ 2) κ cg cm cT ε εs C₀ C₂ Cq0 Cl0 cS0)
    (ht : Hist.InDh ((L : ℝ) ^ 2) β δ κ cg cm cT ε Nh (Hist.traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
    (hA2 : 2 ≤ R.A) (hr1 : cR R ((L : ℝ) ^ 2) cm C₂ * ε ≤ 1) (hk1 : 8 * cx κ cT * ε ≤ 1)
    {k : ℕ} (hk : k < Nh) (a : Lam 2 L N) :
    let t := Hist.traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    ‖(Obs2.nuFH R t (k + 1) - (Obs2.nuFH R t k + 4 * Obs2.gH R t k * Obs2.dlH R t k)) *
        ∑ i ∈ range (k + 1), Obs2.rowS (Obs2.histCovO R t i) a‖ ≤
      nuB L Cq Cl cS (cx κ cT) (cR R ((L : ℝ) ^ 2) cm C₂) c * (t k).1 ^ 2 +
        nuB L Cq Cl cS (cx κ cT) (cR R ((L : ℝ) ^ 2) cm C₂) c * (t k).1 * zA L R.msq k := by
  intro t
  have hL0 := X.L_pos
  have hL7 := X.L7
  have hℓ : 0 < R.ℓ := Fact.out
  have hc0 := X.c_nonneg
  have htk : Hist.InDh ((L : ℝ) ^ 2) β δ κ cg cm cT ε k t :=
    ⟨fun i hi => ht.1 i (by omega), fun i hi => ht.2 i (by omega)⟩
  obtain ⟨-, HI, hg0, hgε, hz, hy, hη2, hηs, hWl, hDx, hvr, hwr, hr0, hrε, hcW, -, -⟩ :=
    hist_raw R hSB X.hV hm hβ hδ1 H t k hk htk
  set st := rawHist R k t with hst
  set g := (t k).1 with hgd
  set x := (t k).2.2 with hxd
  set r := cR R ((L : ℝ) ^ 2) cm C₂ * g with hrd
  have hρ1 : R.ρ < 1 := by linarith [X.hρ8]
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  have hK : Knorm k (fscale st.Z * R.ℓ) R.A (rawK R st.u x) ≤ ENNReal.ofReal ‖x.2‖ :=
    le_of_eq (Knorm_rawK R HI.hu hZ x)
  obtain ⟨-, -, -, hx⟩ := ht.1 k hk.le
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
  have hg1 : g ≤ 1 := (X.hg k hk.le).2
  have hcx : 0 ≤ cx κ cT := H.hcx
  have hg3 : g ^ 3 ≤ g ^ 2 := by
    rw [pow_succ]; exact mul_le_of_le_one_right (sq_nonneg g) hg1
  have hr1' : r ≤ 1 := hrε.trans hr1
  have hk1' : 8 * ‖x.2‖ ≤ 1 := by
    have h1 : g ^ 3 ≤ ε := by
      have := pow_le_pow_left₀ hg0 hgε 3
      have hε1 : ε ≤ 1 := H.hε1
      have : ε ^ 3 ≤ ε := by
        rw [pow_succ]; exact mul_le_of_le_one_left (H.hε.le) (pow_le_one₀ H.hε.le hε1)
      linarith
    have := mul_le_mul_of_nonneg_left h1 hcx
    linarith
  have hstep := hNu N R k (X.hV k hk) st HI g (t k).2.1 (rawD R st.u x) (rawK R st.u x)
    (rawD_mem R _ _) (rawK_mem R _ _) (hm k hk) hg0 (cZ R * g) hz hy hη2 hηs R.A
    (cW R ((L : ℝ) ^ 2) cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r hA2 (by positivity) (norm_nonneg _)
    (norm_nonneg _) hWl hDx hK hvr hwr hr1' hk1'
  -- the next `ν♭`
  set D := rawD R st.u x
  set K := rawK R st.u x
  have hμ1 : (t (k + 1)).2.1 = (histOut R k t).nu.re := by
    show (Hist.traj (rgData R) ((L : ℝ) ^ 2) b μ₀ (k + 1)).2.1 = _
    rw [traj_succ_rg]
    show (L : ℝ) ^ 2 * (t k).2.1 + ((histOut R k t).nu.re - (L : ℝ) ^ 2 * (t k).2.1) = _
    ring
  have hreal : (((histOut R k t).nu.re : ℝ) : ℂ) = (histOut R k t).nu :=
    Complex.conj_eq_iff_re.1 (traj_out_real R X.hρ0 hρ1 ((L : ℝ) ^ 2) b μ₀ k).1
  have hZ2 : stZ' R (rawHist R (k + 1) t) = stZ2 R k st g (t k).2.1 D K := rfl
  have hZ2ne : stZ2 R k st g (t k).2.1 D K ≠ 0 := by
    rw [← hZ2]
    have := X.zpos (k + 1 + 1)
    exact norm_pos_iff.1 this
  have hstNu : stNu R (k + 1) (rawHist R (k + 1) t) (t (k + 1)).2.1 = stCv R k st g (t k).2.1 D K 2 := by
    unfold stNu
    rw [hμ1, hreal, hZ2]
    show stCv R k st g (t k).2.1 D K 2 * (L : ℂ) ^ (2 * (k + 1)) / stZ2 R k st g (t k).2.1 D K *
      stZ2 R k st g (t k).2.1 D K / (L : ℂ) ^ (2 * (k + 1)) = _
    have hL : (L : ℂ) ^ (2 * (k + 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
    field_simp
  have hnext : Obs2.nuFH R t (k + 1) =
      stCv R k st g (t k).2.1 D K 2 - stA R (rawHist R (k + 1) t) * R.msq := by
    unfold Obs2.nuFH; rw [hstNu]
  set E := stCv R k st g (t k).2.1 D K 2 -
    (Obs2.nuFH R t k + 4 * Obs2.gH R t k * Obs2.dlH R t k) with hEd
  have hE : ‖E‖ ≤ _ := hstep
  have e1 : Obs2.nuFH R t (k + 1) - (Obs2.nuFH R t k + 4 * Obs2.gH R t k * Obs2.dlH R t k) =
      E - stA R (rawHist R (k + 1) t) * R.msq := by rw [hnext, hEd]; ring
  rw [e1, norm_mul]
  -- the pieces
  have hS := X.S_le hk a
  set a0 := zH R t k
  set a1 := zH R t (k + 1)
  have ha0 : 0 < a0 := X.zpos k
  have ha1 : 0 < a1 := X.zpos (k + 1)
  have hrat : a0 / a1 ≤ 8 / 7 := by
    have := zH_ratio_down R X.hρ0 X.hρ8 t (show k ≤ k + 1 by omega)
    rw [show k + 1 - k = 1 by omega, pow_one] at this
    rw [div_le_iff₀ ha1]; linarith
  have hrat0 : 0 ≤ a0 / a1 := by positivity
  set Pk := ((L : ℝ) ^ k) ^ 2
  have hPk : 0 < Pk := by positivity
  have hP : ((L : ℝ) ^ (k + 1)) ^ 2 = Pk * (L : ℝ) ^ 2 := by rw [pow_succ]; ring
  have hfs : (fscale st.Z * R.ℓ) ^ 2 = R.ℓ ^ 2 / a0 := by
    rw [mul_pow, fscale_sq]; ring
  have hfs4 : (fscale st.Z * R.ℓ) ^ 4 = (R.ℓ ^ 2 / a0) ^ 2 := by rw [← hfs]; ring
  have hfs' : (fscale (stZ' R st) * R.ℓ) ^ 2 = R.ℓ ^ 2 / a1 := by
    have e : ‖stZ' R st‖ = a1 := rfl
    rw [mul_pow, fscale_sq, e]; ring
  rw [hfs, hfs4, hfs', hP] at hE
  have hdl := X.dl_le hk
  rw [hP] at hdl
  rw [hP] at hS
  obtain ⟨RQ, hRQd⟩ : ∃ RQ, RQ = cS * (Cl * (8 * ‖x.2‖)) := ⟨_, rfl⟩
  obtain ⟨sg, hsgd⟩ : ∃ sg, sg = BH.sig 2 L (cM * R.ℓ ^ 2 * (2 * |(t k).2.1| + 2 * (cZ R * g)) +
    8 * R.ℓ ^ 4 * g) (cW R ((L : ℝ) ^ 2) cm C₂ * g ^ 2 + ‖x.1‖) := ⟨_, rfl⟩
  rw [← hRQd, ← hsgd] at hE
  have hRQ0 : 0 ≤ RQ := by rw [hRQd]; positivity
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have hN0 : 0 ≤ cNear 2 L := Nat.cast_nonneg _
  have hv0 : 0 ≤ cM * R.ℓ ^ 2 * (2 * |(t k).2.1| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g := by
    have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
    have : 0 ≤ cZ R := by unfold cZ; positivity
    positivity
  have hsig : sg ≤ (cNear 2 L * Q1 2 ^ 2 + Q1 2) * r ^ 2 := by
    rw [hsgd]
    unfold BH.sig
    have h1 := pow_le_pow_left₀ hv0 hvr 2
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hN0 (sq_nonneg (Q1 2)))
    have h3 := mul_le_mul_of_nonneg_left hwr (by linarith : (0 : ℝ) ≤ Q1 2)
    linarith
  have hQc : 0 ≤ cNear 2 L * Q1 2 ^ 2 + Q1 2 :=
    add_nonneg (mul_nonneg hN0 (sq_nonneg _)) (by linarith)
  have hsg0 : 0 ≤ sg := by
    rw [hsgd]; unfold BH.sig
    have h1 : 0 ≤ cW R ((L : ℝ) ^ 2) cm C₂ * g ^ 2 + ‖x.1‖ := by positivity
    have h2 : 0 ≤ cNear 2 L * Q1 2 ^ 2 *
        (cM * R.ℓ ^ 2 * (2 * |(t k).2.1| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g) ^ 2 :=
      mul_nonneg (mul_nonneg hN0 (sq_nonneg _)) (sq_nonneg _)
    have h3 : 0 ≤ Q1 2 * (cW R ((L : ℝ) ^ 2) cm C₂ * g ^ 2 + ‖x.1‖) := mul_nonneg (by linarith) h1
    linarith
  obtain ⟨RL, hRLd⟩ : ∃ RL, RL = Cl * ((L : ℝ) ^ 2 * sg) := ⟨_, rfl⟩
  rw [← hRLd] at hE
  have hRL0 : 0 ≤ RL := by rw [hRLd]; positivity
  have halg := nuflow_alg (Cq := Cq) (RQ := RQ) (RL := RL) (a := a0) (a' := a1) (ℓ := R.ℓ)
    (Pk := Pk) (L2 := (L : ℝ) ^ 2) (Sb := 27 / 16 * R.ℓ ^ 2 * (Pk * (L : ℝ) ^ 2) / a1)
    (dl := ‖Obs2.dlH R t k‖) hCq hRQ0 hRL0 ha0 ha1 hℓ hPk (by positivity) hdl (norm_nonneg _) rfl
  have hES : ‖E‖ * ‖∑ i ∈ range (k + 1), Obs2.rowS (Obs2.histCovO R t i) a‖ ≤
      27 / 16 * Cq * RQ * (L : ℝ) ^ 2 * (a0 / a1) + 27 / 128 * Cq * RQ * (a0 / a1) ^ 2 +
        27 / 16 * Cq * RL :=
    (mul_le_mul hE hS (norm_nonneg _) (le_trans (norm_nonneg _) hE)).trans halg
  -- the `a m²` term
  have hζ1 : ‖zetaH R (k + 1) t‖ ≤ 4 * cz' * g := by
    refine (X.hζ (k + 1) (by omega)).trans ?_
    have := X.hg2 k hk; have := X.hcz
    nlinarith
  have hA' : ‖stA R (rawHist R (k + 1) t) * (R.msq : ℂ)‖ ≤ a1 * (4 * cz' * g) * R.msq := by
    unfold stA
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg X.hm0]
    have e : stZeta R (rawHist R (k + 1) t) = zetaH R (k + 1) t := rfl
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hζ1 ha1.le) X.hm0
  have hmP : R.msq * (Pk * (L : ℝ) ^ 2) ≤ zA L R.msq k := by
    rw [← hP]
    refine mP_le_zA X.hm0 (by linarith) (le_trans ?_ X.hm)
    refine mul_le_mul_of_nonneg_left ?_ X.hm0
    rw [show (L : ℝ) ^ 2 = ((L : ℝ) ^ 1) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega)) 2
  have hAS : ‖stA R (rawHist R (k + 1) t) * (R.msq : ℂ)‖ *
      ‖∑ i ∈ range (k + 1), Obs2.rowS (Obs2.histCovO R t i) a‖ ≤ 7 * c * (g * zA L R.msq k) := by
    have hcz0 := X.hcz
    refine (mul_le_mul hA' hS (norm_nonneg _)
      (mul_nonneg (mul_nonneg ha1.le (by positivity)) X.hm0)).trans ?_
    have e : a1 * (4 * cz' * g) * R.msq * (27 / 16 * R.ℓ ^ 2 * (Pk * (L : ℝ) ^ 2) / a1) =
        27 / 4 * (R.ℓ ^ 2 * cz') * g * (R.msq * (Pk * (L : ℝ) ^ 2)) := by
      field_simp; ring
    rw [e]
    have hcz2 := X.hcz2
    have h1 : 27 / 4 * (R.ℓ ^ 2 * cz') * g * (R.msq * (Pk * (L : ℝ) ^ 2)) ≤
        27 / 4 * c * g * zA L R.msq k := by
      have : 0 ≤ R.msq * (Pk * (L : ℝ) ^ 2) := mul_nonneg X.hm0 (by positivity)
      have := X.hcz
      gcongr
    have : 0 ≤ c * g * zA L R.msq k := mul_nonneg (mul_nonneg hc0 hg0) (zA_nonneg L X.hm0 k)
    nlinarith
  -- assemble
  refine (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)).trans ?_
  rw [add_mul]
  have hRQb : RQ ≤ 8 * cS * Cl * cx κ cT * g ^ 2 := by
    rw [hRQd]
    have h1 : ‖x.2‖ ≤ cx κ cT * g ^ 2 := hx2.trans (mul_le_mul_of_nonneg_left hg3 hcx)
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 8 * cS * Cl)
    calc cS * (Cl * (8 * ‖x.2‖)) = 8 * cS * Cl * ‖x.2‖ := by ring
      _ ≤ 8 * cS * Cl * (cx κ cT * g ^ 2) := this
      _ = _ := by ring
  have hRLb : RL ≤ Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) *
      cR R ((L : ℝ) ^ 2) cm C₂ ^ 2 * g ^ 2 := by
    rw [hRLd]
    have := mul_le_mul_of_nonneg_left hsig (by positivity : (0 : ℝ) ≤ Cl * (L : ℝ) ^ 2)
    calc Cl * ((L : ℝ) ^ 2 * sg) = Cl * (L : ℝ) ^ 2 * sg := by ring
      _ ≤ Cl * (L : ℝ) ^ 2 * ((cNear 2 L * Q1 2 ^ 2 + Q1 2) * r ^ 2) := this
      _ = _ := by rw [hrd]; ring
  have hL2 : (49 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have t1 : 27 / 16 * Cq * RQ * (L : ℝ) ^ 2 * (a0 / a1) + 27 / 128 * Cq * RQ * (a0 / a1) ^ 2 ≤
      16 * (L : ℝ) ^ 2 * Cq * cS * Cl * cx κ cT * g ^ 2 := by
    have hCRQ : 0 ≤ Cq * RQ := mul_nonneg hCq hRQ0
    have h1 : 27 / 16 * Cq * RQ * (L : ℝ) ^ 2 * (a0 / a1) ≤
        27 / 16 * (Cq * RQ) * (L : ℝ) ^ 2 * (8 / 7) := by
      have := mul_le_mul_of_nonneg_left hrat (by positivity : (0 : ℝ) ≤ 27 / 16 * (Cq * RQ) * (L : ℝ) ^ 2)
      calc 27 / 16 * Cq * RQ * (L : ℝ) ^ 2 * (a0 / a1) = 27 / 16 * (Cq * RQ) * (L : ℝ) ^ 2 * (a0 / a1) := by ring
        _ ≤ _ := this
    have h2 : 27 / 128 * Cq * RQ * (a0 / a1) ^ 2 ≤ 27 / 128 * (Cq * RQ) * (8 / 7) ^ 2 := by
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrat0 hrat 2)
        (by positivity : (0 : ℝ) ≤ 27 / 128 * (Cq * RQ))
      calc 27 / 128 * Cq * RQ * (a0 / a1) ^ 2 = 27 / 128 * (Cq * RQ) * (a0 / a1) ^ 2 := by ring
        _ ≤ _ := this
    have h3 : Cq * RQ ≤ Cq * (8 * cS * Cl * cx κ cT * g ^ 2) := mul_le_mul_of_nonneg_left hRQb hCq
    have h5 : 27 / 16 * (Cq * RQ) * (L : ℝ) ^ 2 * (8 / 7) + 27 / 128 * (Cq * RQ) * (8 / 7) ^ 2 ≤
        2 * (L : ℝ) ^ 2 * (Cq * RQ) := by
      have : 27 / 16 * (8 / 7) * (L : ℝ) ^ 2 + 27 / 128 * (8 / 7) ^ 2 ≤ 2 * (L : ℝ) ^ 2 := by
        nlinarith
      have := mul_le_mul_of_nonneg_right this hCRQ
      linarith
    have h6 : 2 * (L : ℝ) ^ 2 * (Cq * RQ) ≤ 2 * (L : ℝ) ^ 2 * (Cq * (8 * cS * Cl * cx κ cT * g ^ 2)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have e : 2 * (L : ℝ) ^ 2 * (Cq * (8 * cS * Cl * cx κ cT * g ^ 2)) =
        16 * (L : ℝ) ^ 2 * Cq * cS * Cl * cx κ cT * g ^ 2 := by ring
    linarith
  have t2 : 27 / 16 * Cq * RL ≤ 2 * Cq * Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) *
      cR R ((L : ℝ) ^ 2) cm C₂ ^ 2 * g ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hRLb hCq
    have h0 : 0 ≤ Cq * (Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) *
      cR R ((L : ℝ) ^ 2) cm C₂ ^ 2 * g ^ 2) :=
      mul_nonneg hCq (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCl (sq_nonneg _)) hQc)
        (sq_nonneg _)) (sq_nonneg _))
    have e : 2 * Cq * Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) *
      cR R ((L : ℝ) ^ 2) cm C₂ ^ 2 * g ^ 2 = 2 * (Cq * (Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) *
      cR R ((L : ℝ) ^ 2) cm C₂ ^ 2 * g ^ 2)) := by ring
    have hCRL : 0 ≤ Cq * RL := mul_nonneg hCq hRL0
    rw [e]
    linarith
  have hB : nuB L Cq Cl cS (cx κ cT) (cR R ((L : ℝ) ^ 2) cm C₂) c * g ^ 2 =
      16 * (L : ℝ) ^ 2 * Cq * cS * Cl * cx κ cT * g ^ 2 + 2 * Cq * Cl * (L : ℝ) ^ 2 *
        (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cR R ((L : ℝ) ^ 2) cm C₂ ^ 2 * g ^ 2 + 7 * c * g ^ 2 := by
    unfold nuB; ring
  have hB2 : 7 * c * (g * zA L R.msq k) ≤
      nuB L Cq Cl cS (cx κ cT) (cR R ((L : ℝ) ^ 2) cm C₂) c * g * zA L R.msq k := by
    have h0 : 7 * c ≤ nuB L Cq Cl cS (cx κ cT) (cR R ((L : ℝ) ^ 2) cm C₂) c := by
      unfold nuB
      have : 0 ≤ 16 * (L : ℝ) ^ 2 * Cq * cS * Cl * cx κ cT := by positivity
      have : 0 ≤ 2 * Cq * Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) *
        cR R ((L : ℝ) ^ 2) cm C₂ ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCq) hCl)
          (sq_nonneg _)) hQc) (sq_nonneg _)
      linarith
    have := mul_le_mul_of_nonneg_right h0 (mul_nonneg hg0 (zA_nonneg L X.hm0 k))
    linarith [show nuB L Cq Cl cS (cx κ cT) (cR R ((L : ℝ) ^ 2) cm C₂) c * (g * zA L R.msq k) =
      nuB L Cq Cl cS (cx κ cT) (cR R ((L : ℝ) ^ 2) cm C₂) c * g * zA L R.msq k by ring]
  have h7 : 0 ≤ 7 * c * g ^ 2 := by positivity
  linarith

end C2Ctx

end

end Spin2
