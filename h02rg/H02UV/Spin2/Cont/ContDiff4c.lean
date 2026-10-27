import Spin2.Cont.ContDiff4b
import PtCorr2.Restart.Restart3b

/-!
# B3, T6: the restarted product versus the reference product; the relative form of `cd3_restartM`

Along every admissible trajectory (`MasterFacts`):

* **`MasterFacts.cd4_prod_cmp`**: for every observable restart datum `o'` at scale `k` and
  `k + j ≤ N_h`, `∏_{i<j}|1 − 𝔫F_{k+i}| ≤ exp((8/7)(8/3)(2/L))·∏_{i<j}|1 − 𝔫^{P'}_{k+i}|`
  (`𝔫^{P'} = nn2 R P' V`, any `V`; memory term `(4/3)q·2^{-i}` with `q = 2/L` from `M.tad`,
  `|𝔫| ≤ 1/8` from `M.loop`).
* **`MasterFacts.cd4_ratio`**: `exp(−2c_δ(4/β_L)ε)|β^{P'}_k|∏_{i<j}|1 − 𝔫^{P'}_{k+i}| ≤ |β^{P'}_{k+j}|`
  (`bt2_flow`, `M.relG`, `M.ginc`; `c_δ = core.cRel`).
* **`cd3_restartRel`**: under the hypotheses of `cd3_restartM`, for `j ≤ N_h − k`,
  `|β^δ_{k+j}|·|β^{P'}_k| ≤ (4/3)M^δ·exp((8/7)(8/3)(2/L))·exp(2c_δ(4/β_L)ε)·|β^{P'}_{k+j}|`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 1000000 in
/-- **The restarted product versus the reference product.** -/
theorem MasterFacts.cd4_prod_cmp (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (P' : ObsPts 2 L N) (V : OCoup .two) (o' : ObsSt .two L N) (h0 : o'.IsObs) {k j : ℕ}
    (hkj : k + j ≤ Nh) :
    ∏ i ∈ range j, ‖1 - frakN2F P' (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (histVF2 (R.withMsq m) P' k o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) k (k + i)‖ ≤
      Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ)))) *
        ∏ i ∈ range j, ‖1 - nn2 R P' V m b μ₀ (k + i)‖ := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨-, hT, hBg⟩ := M.tad N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  obtain ⟨-, -, q, -, -, hloop⟩ := M.loop N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P' V
  have hL8 : (8 : ℝ) ≤ L := by exact_mod_cast (show 8 ≤ L by have := M.core.hL49; omega)
  have hq0 : (0 : ℝ) ≤ 2 / L := by positivity
  have hq4 : (2 : ℝ) / L ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hsub := fun i (hi : i < j) => r3_frakN2F_sub_le (R.withMsq m) P' k o' t h0
    (obsInit .two V P') (obsInit_isObs .two V P') (n := Nh) (Bτ := M.core.ce) hq0 hq4
    (fun k' j' hkj' hj' => hT P' V k' j' hkj' hj'.le) (fun k' hk' => hBg k' hk'.le)
    (i := k + i) (by omega) (by omega)
  have h := r3_prod_cmp
    (fun i => frakN2F P' (histCovO (R.withMsq m) t) (histVF2 (R.withMsq m) P' k o' t) k (k + i))
    (fun i => nn2 R P' V m b μ₀ (k + i)) (fun i => 4 / 3 * (2 / (L : ℝ)) * (1 / 2) ^ i) j
    (fun i hi => by
      have := hsub i hi
      rw [show k + i - k = i by omega] at this
      exact this)
    (fun i hi => (hloop (k + i) (by omega)).1)
  refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
    (prod_nonneg fun _ _ => norm_nonneg _))
  rw [← mul_sum]
  have := r3_geom_half j
  have h2 : 4 / 3 * (2 / (L : ℝ)) * ∑ i ∈ range j, (1 / 2 : ℝ) ^ i ≤ 4 / 3 * (2 / (L : ℝ)) * 2 :=
    mul_le_mul_of_nonneg_left this (by positivity)
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The reference product is the ratio of the couplings**:
`exp(−2c_δ(4/β_L)ε)|β_k|∏_{i<j}|1 − 𝔫_{k+i}| ≤ |β_{k+j}|`. -/
theorem MasterFacts.cd4_ratio (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (P' : ObsPts 2 L N) (V : OCoup .two) (hmu : OCoup2.mua V ≠ 0) {k j : ℕ} (hkj : k + j ≤ Nh) :
    Real.exp (-(2 * (M.core.cRel * (4 / betaL L) * M.core.ε))) * ‖bt2 R P' V m b μ₀ k‖ *
        ∏ i ∈ range j, ‖1 - nn2 R P' V m b μ₀ (k + i)‖ ≤ ‖bt2 R P' V m b μ₀ (k + j)‖ := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have hrel := M.relG N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P' V hmu
  have hginc := M.ginc N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  obtain ⟨hcR, -⟩ := M.core.consts_nonneg
  have hβ2 := betaL_ge (show 8 ≤ L by have := M.core.hL49; omega)
  have hβp : 0 < betaL L := by linarith
  have hlow := r3_beta_lower (fun i => bt2 R P' V m b μ₀ i) (fun i => nn2 R P' V m b μ₀ i)
    (fun i => err2 R P' V m b μ₀ i) (fun i => M.core.cRel * (t i).1 ^ 2) k Nh
    (fun i hi => bt2_flow R P' V (show Nh < N by omega) m b μ₀ hi)
    (fun i hi => (hrel i hi).1) (fun i _ => mul_nonneg hcR (sq_nonneg _))
    (fun i hi => by have := (hrel i hi).2; linarith) j hkj
  refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.2 ?_) (norm_nonneg _)) (prod_nonneg fun _ _ => norm_nonneg _)) hlow
  have hs := r3_gsq_sum (fun i => (t i).1) (β := betaL L) k (n := Nh) hginc j hkj
  have hgk : 0 < (t k).1 := (hadm.1 k (by omega)).1
  have hgε : (t (k + j)).1 ≤ M.core.ε := (hadm.1 (k + j) hkj).2.1
  rw [← mul_sum]
  have hS : ∑ i ∈ range j, (t (k + i)).1 ^ 2 ≤ 4 / betaL L * M.core.ε := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hβp]
    have : betaL L / 4 * ∑ i ∈ range j, (t (k + i)).1 ^ 2 ≤ M.core.ε := by
      linarith
    linarith
  have := mul_le_mul_of_nonneg_left hS hcR
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **T6, relative form**: the restarted coupling of the difference datum at scale `k + j` is
`≤ (4/3)M^δ C_mem C_rel |β^{P'}_{k+j}|/|β^{P'}_k|`. -/
theorem cd3_restartRel (M : MasterFacts L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (P P' : ObsPts 2 L N) (V : OCoup .two) (hga : OCoup2.ga V = 0) (hmu : OCoup2.mua V ≠ 0)
    {k r : ℕ} (hk0 : 0 < k) (hkN : k < Nh) (hrk : r ≤ k)
    (hab : blk k P.a = blk k P'.a) (hPb : P.b = P'.b)
    (hdist : supNorm (P.a - P'.a) ≤ L ^ (k - r))
    (hs0 : 0 ≤ M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k))
    (hs : M.csmK * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) ≤ 1 / 2)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) * 2) ≤
      1 / 1344)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 3) ≤ 1) :
    ∀ j ≤ Nh - k,
      ‖betaTot2 (L := L) (N := N) (k + j) (histVF2 (R.withMsq m) P' k
          (cd3Delta (R.withMsq m) P P' V k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (k + j))‖ * ‖bt2 R P' V m b μ₀ k‖ ≤
        4 / 3 * M.cd3M (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 (zA L m k)
            ‖bt2 R P V m b μ₀ k‖ ‖bt2 R P' V m b μ₀ k‖
            (histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (rpIota 0 0)
            (R.withMsq m).A r *
          Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ)))) *
          Real.exp (2 * (M.core.cRel * (4 / betaL L) * M.core.ε)) * ‖bt2 R P' V m b μ₀ (k + j)‖ := by
  intro j hj
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have h1 := cd3_restartM M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P P' V hga hmu hk0 hkN
    hrk hab hPb hdist hs0 hs hg hreg j hj
  have hval : ∀ j' < k + 1, ValidCore (R.withMsq m) j' ∧ RawInv (R.withMsq m) j'
      (rawHist (R.withMsq m) j' t) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCN⟩ := id M.core.hC2
    obtain ⟨hV, -⟩ := (hCN N R hP hi0 hRℓ hRA hRρ hN Nh hNh).2.2.2.2.2.2.2.2.2 m hm
    exact hist_valid (R.withMsq m) hV t (n := k + 1) (by omega)
  obtain ⟨h0, -⟩ := cd3_struct (R.withMsq m) P P' V hga k t hval hab hPb
  have h2 := M.cd4_prod_cmp N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P' V _ h0
    (k := k) (j := j) (by omega)
  have h3 := M.cd4_ratio N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P' V hmu
    (k := k) (j := j) (by omega)
  set X := 4 / 3 * M.cd3M (t k).1 (zA L m k) ‖bt2 R P V m b μ₀ k‖ ‖bt2 R P' V m b μ₀ k‖
    (histS (R.withMsq m) k t) (rpIota 0 0) (R.withMsq m).A r
  set Pn := ∏ i ∈ range j, ‖1 - nn2 R P' V m b μ₀ (k + i)‖
  set Cm := Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ))))
  set y := 2 * (M.core.cRel * (4 / betaL L) * M.core.ε)
  set β0 := ‖bt2 R P' V m b μ₀ k‖
  set βj := ‖bt2 R P' V m b μ₀ (k + j)‖
  set δj := ‖betaTot2 (L := L) (N := N) (k + j) (histVF2 (R.withMsq m) P' k
    (cd3Delta (R.withMsq m) P P' V k t) t (k + j))‖
  have hX0 : 0 ≤ X := by
    have h10 := cd3_restartM M N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P P' V hga hmu hk0
      hkN hrk hab hPb hdist hs0 hs hg hreg 0 (Nat.zero_le _)
    rw [range_zero, prod_empty, mul_one] at h10
    exact (norm_nonneg _).trans h10
  have hey : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have hβ0 : 0 ≤ β0 := norm_nonneg _
  have hδ : δj ≤ X * (Cm * Pn) := h1.trans (mul_le_mul_of_nonneg_left h2 hX0)
  have hPi : β0 * Pn ≤ Real.exp y * βj := by
    have hp : 0 < Real.exp y := Real.exp_pos _
    have := mul_le_mul_of_nonneg_left h3 hp.le
    calc β0 * Pn = Real.exp y * (Real.exp (-y) * β0 * Pn) := by
          rw [← mul_assoc, ← mul_assoc, mul_comm (Real.exp y), hey, one_mul]
      _ ≤ _ := this
  calc δj * β0 ≤ X * (Cm * Pn) * β0 := mul_le_mul_of_nonneg_right hδ hβ0
    _ = X * Cm * (β0 * Pn) := by ring
    _ ≤ X * Cm * (Real.exp y * βj) :=
        mul_le_mul_of_nonneg_left hPi (mul_nonneg hX0 (Real.exp_pos _).le)
    _ = X * Cm * Real.exp y * βj := by ring
    _ = _ := rfl

end

end Spin2
