import PtCorr2.Last.LastObsK5
import Step2.Last.LastNRG
import PtCorr2.Obs.KObsStep
import PtCorr2.Obs.ConstSplitHist
import PtCorr2.Obs.ObsHistLast

/-!
# The inputs of the last step at the raw level

For the last step `j + 1 = N` driven by a raw state with inactive clamps (as in
`Step2.LastN.rg_last_bounds`):

* **`bulk_last_in`**: `‖V♭‖_j ≤ v = c_Mℓ²(2|μ| + 2η) + 8ℓ⁴g`, `‖W^{lin} + D‖_j ≤ w_l + d_d`,
  `‖K♭‖_{j,A/2} ≤ 8k`, and the memberships `V♭, W^{lin} + D ∈ 𝓑`, `K♭ ∈ 𝒜` (`InF`, `InK2`,
  `ε(V♭(B)) = 0`);
* **`olocS_last`**: the locality of the full inputs (copy of `olocS_full` under `ValidLast`);
* `obs_last_in`: the observable parts of the full inputs (`w_a`-weight):
  `‖V^{obs}_{full}‖ ≤ ‖V^{obs}‖`, `‖𝒲^{obs}_{full}‖ ≤ ‖𝒲^{obs}‖`,
  `(A/2)^{(|𝓑(X)|-4)_+}‖K^{obs}_{full}(X)‖ ≤ 8A^{(|𝓑(X)|-4)_+}‖K^{obs}(X)‖`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 2000000 in
/-- **The bulk inputs of the last step.** -/
theorem bulk_last_in (R : RGPar 2 L N) {j : ℕ} (hV : LastN.ValidLast R j) (hL8 : 2 ^ (2 + 3) + 8 * 2 < L)
    {st : RawSt 2 L N} (H : RawInv R j st) (g μ : ℝ) {D : Fam 2 L N} {K : Act 2 L N}
    (hD : D ∈ BSub (L := L) (N := N) j) (hK : K ∈ ASub (L := L) (N := N) j)
    (hm : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) (hg0 : 0 ≤ g) (η : ℝ) (hz : ‖st.z / st.Z‖ ≤ η)
    (hy : ‖st.y / st.Z‖ ≤ η) (hη : 2 * η ≤ R.ρ) (hηs : 8 * cM * R.ℓ ^ 2 * η ≤ 1 / 2)
    {A wl dd k : ℝ} (hA : 0 < A) (hwl0 : 0 ≤ wl) (hdd0 : 0 ≤ dd)
    (hWl : Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl)
    (hDd : Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd)
    (hKk : Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal k) :
    Fnorm j (fscale st.Z * R.ℓ) (stVf R j st g μ) ≤
      ENNReal.ofReal (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) ∧
    Fnorm j (fscale st.Z * R.ℓ) (st.Wl + D) ≤ ENNReal.ofReal (wl + dd) ∧
    Knorm j (fscale st.Z * R.ℓ) (A / 2) (Kflat j (stDelta R j st) K) ≤ ENNReal.ofReal (8 * k) ∧
    InF j (stVf R j st g μ) ∧ (∀ b, ε (stVf R j st g μ b : Alg 2 L N) = 0) ∧
    InF j (st.Wl + D) ∧ InK2 j (Kflat j (stDelta R j st) K) ∧
    Fnorm j (fscale st.Z * R.ℓ) (stDelta R j st) ≤ ENNReal.ofReal (8 * cM * R.ℓ ^ 2 * η) := by
  have hV' := hV
  obtain ⟨hjN, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hz
  have hj : j < N := by omega
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
  have hVmem := VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hj
    (stKap R j st g μ).toVec
  have hVf_mem : stVf R j st g μ ∈ BSub (L := L) (N := N) j := by
    rw [stVf_eq_kap]; exact hVmem
  have hgr := norm_stGr_le R j st g μ
  rw [abs_of_nonneg hg0] at hgr
  have hrZ : ‖stZ' R st / st.Z‖ ≤ 9 / 8 := by
    have e : stZ' R st / st.Z = 1 + stZeta R st := by
      unfold stZ'; rw [mul_div_cancel_left₀ _ hZ]
    rw [e]; refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
  have hVv : Fnorm j (fscale st.Z * R.ℓ) (stVf R j st g μ) ≤
      ENNReal.ofReal (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) := by
    have e : stVf R j st g μ = VfamL j ![0, 0, (μ : ℂ) * stZ' R st / (L : ℂ) ^ (2 * j) -
        stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2] := stVf_eq hZ hzy hyc
    rw [e]
    refine (Fnorm_VfamL_norm2 j hj.le hℓ hZ _ 0 0 _ _ μ R.msq).trans
      (ENNReal.ofReal_le_ofReal ?_)
    simp only [zero_div, norm_zero, add_zero]
    rw [norm_stA_div hZ]
    have : ‖stZeta R st‖ * |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 2 * η := by
      rw [mul_assoc]
      calc ‖stZeta R st‖ * (|R.msq| * ((L : ℝ) ^ j) ^ 2) ≤ 2 * η * 1 := by gcongr
        _ = 2 * η := mul_one _
    have h1 : ‖stZ' R st / st.Z‖ * |μ| ≤ 2 * |μ| := by
      have := mul_le_mul_of_nonneg_right hrZ (abs_nonneg μ); linarith [abs_nonneg μ]
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
    nlinarith
  have hw : Fnorm j (fscale st.Z * R.ℓ) (st.Wl + D) ≤ ENNReal.ofReal (wl + dd) :=
    Fnorm_add_le _ _ hwl0 hdd0 hWl hDd
  set δΔ := 8 * cM * R.ℓ ^ 2 * η with hδΔ
  have hδΔ0 : 0 ≤ δΔ := by
    have := (Nat.cast_nonneg (α := ℝ) (Fintype.card (Mono 2))); positivity
  have hΔ : Fnorm j (fscale st.Z * R.ℓ) (stDelta R j st) ≤ ENNReal.ofReal δΔ := by
    refine (Fnorm_stDelta_le hj.le hℓ hZ (2 * η) hζη
      (by rw [stYc_eq hZ hyc]; linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 2 * η * |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 2 * η := by
      rw [mul_assoc]
      calc 2 * η * (|R.msq| * ((L : ℝ) ^ j) ^ 2) ≤ 2 * η * 1 := by gcongr
        _ = 2 * η := mul_one _
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    rw [hδΔ]
    nlinarith [mul_nonneg hM (sq_nonneg R.ℓ)]
  have hKf := Knorm_stKflat_le (R := R) j hsℓ hA.le hδΔ0 st hΔ K
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
  have hKfmem := Kflat_mem hj (VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hj _)
    (eps_stDelta R j st) hK
  refine ⟨hVv, hw, hKflat, hVf_mem.1, fun b => ?_, (add_mem H.hWl hD).1, hKfmem.1, hΔ⟩
  exact eps_VfamL j _ b

/-- **The full inputs of the last step are local** (copy of `olocS_full` under `ValidLast`). -/
theorem olocS_last {c : Obs.Case} (R : RGPar 2 L N) (P : ObsPts 2 L N) {j : ℕ} {st : RawSt 2 L N}
    (g μ : ℝ) {D : Fam 2 L N} {K : Act 2 L N} {o : ObsSt c L N}
    (hV : LastN.ValidLast R j) (H : RawInv R j st) (hD : D ∈ BSub (L := L) (N := N) j)
    (hK : K ∈ ASub (L := L) (N := N) j) (ho : ObsLocInv P j o) :
    OLocS P j (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) := by
  obtain ⟨hj1, hd, hL, -, -, -, -⟩ := hV
  have hjN : j < N := by omega
  have hVm := VfamL_mem (L := L) (N := N) hd hL hjN ![st.z + stYc R st - stA R st,
    st.y - stYc R st, stNu R j st μ - stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2]
  have hΔm := VfamL_mem (L := L) (N := N) hd hL hjN
    ![stA R st - stYc R st, stYc R st, stA R st * R.msq, 0]
  have hW := (add_mem H.hWl hD).1
  refine ⟨fun b => add_mem (emb_mem_osub (hVm.1.loc b)) (ho.V b),
    fun b => add_mem (emb_mem_osub (hW.loc b)) (ho.W b), fun Y hY => ?_⟩
  have hbp : ((bpow j (fun b => gexp (stDelta R j st b)) Y : EvR (Lam 2 L N)) : Alg 2 L N) ∈
      NX (nbhd j Y : Set (Lam 2 L N)) :=
    coe_prod_mem _ (blocks j Y) _ fun b hb =>
      NX_mono (coe_subset.2 (nbhd_mono (blockSet_subset hY.1 hb)))
        (gexp_mem_NX (eps_stDelta R j st b) (hΔm.1.loc b))
  exact mul_mem (emb_mem_osub hbp) (add_mem (emb_mem_osub (hK.1.loc Y hY)) (ho.K Y hY))

/-- `‖V^{obs}_j(B)‖ ≤ s_j²∑_B|m₂(V_j(B)_a)|` for `j ≥ 1` and any `γ_a` (the states from `V` and
`gaZero V` coincide from scale `1` on, `obsHist_gaZero`). -/
theorem vobs2_block_le' (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
    (V : OCoup .two) (t : Flow2.Hist.Seq (Xs R)) (ht : (t 0).2.2 = 0) {j : ℕ} (hj : 1 ≤ j)
    (hs : 0 < histS R j t) (b : Fin 2 → ℕ) (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo Obs2.wA j (histS R j t) ((obsHist R P (obsInit .two V P) j t).V b) ≤
      ENNReal.ofReal (histS R j t ^ 2 * shA2 (histVO2 R P (obsInit .two V P) t) j) := by
  have hgz := obsHist_gaZero R P t V ht j hj
  have h := vobs2_block_le R P (gaZero V) (gaZero_ga V) t j hs b hb
  have e2 : shA2 (histVO2 R P (obsInit .two (gaZero V) P) t) j =
      shA2 (histVO2 R P (obsInit .two V P) t) j := by
    unfold shA2
    refine sum_congr rfl fun b' _ => ?_
    rw [histVO2_a, histVO2_a, hgz.1]
  rw [hgz.1, ← e2]
  exact h

end

end PtCorr2
