import Spin2.Pair.PairLin4

set_option autoImplicit false

/-!
# B3, T6 (Task 3, comparison): the relative restart size `σ/|β_{a,N_h}|` along `D_ε`

Along `D_ε` (no `Admissible`):

* **`MasterFacts.cw4_prod_cmpD`**: `cd4_prod_cmp` along `D_ε` (`M.tadD`, `M.loopD`):
  `∏_{i<j}|1 − 𝔫F_{k+i}| ≤ exp((8/7)(8/3)(2/L))·∏_{i<j}|1 − 𝔫^{P'}_{k+i}|`;
* **`MasterFacts.cw4_beta_up`**: `|β^{P'}_j| ≤ e^{c}(8/7)^{N_h−j}|β^{P'}_{N_h}|`
  (`c = 2c_δ(4/β_L)ε`; `cw2_ratioD` from `j` to `N_h` and `|𝔫| ≤ 1/8`);
* **`MasterFacts.cw4_sig_cmp`**: for the restart envelope of any observable datum `δ` at `m_r`,
  `σ/|β_{a,N_h}| ≤ cw4Cmp(N_h − j_y)·M₀/|β^{(0,y)}_{m_r}|`,
  `cw4Cmp n = (15/14)^{2n}·exp((8/7)(8/3)(2/L))·e^{2c}·(8/7)^n`
  (`σ = cw2Sig R m b N_h y m_r δ M₀`, `β_{a,N_h} = hBeta R m b (b−m) y N_h`);
* **`MasterFacts.cw4_sig_rel`**: for `δ = pl2Delta` and `M₀ = cddM` (`pl4_T6_inputs`),
  `σ/|β_{a,N_h}| ≤ cw4Cmp(N_h − j_y)·cddRel(K_p, ǧ_{ms}, a_{ms}, rpIota 0 0, A, r)`,
  i.e. `≲_{L, N_h − j_y} ǧ_{ms} + a_{ms} + 48e^{3/2}A·L^{−r}`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

/-- The comparison constant `(15/14)^{2n}·exp((8/7)(8/3)(2/L))·e^{2c}·(8/7)^n`. -/
def cw4Cmp (M : MasterFacts L) (n : ℕ) : ℝ :=
  (15 / 14 : ℝ) ^ (2 * n) * Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ)))) *
    Real.exp (2 * (M.core.cRel * (4 / betaL L) * M.core.ε)) ^ 2 * (8 / 7 : ℝ) ^ n

theorem cw4Cmp_pos (M : MasterFacts L) (n : ℕ) : 0 < cw4Cmp M n := by
  unfold cw4Cmp; positivity

namespace MasterFacts

variable (M : MasterFacts L)

set_option maxHeartbeats 1000000 in
/-- **`cd4_prod_cmp` along `D_ε`.** -/
theorem cw4_prod_cmpD (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P' : ObsPts 2 L N) (V : OCoup .two) (o' : ObsSt .two L N) (h0 : o'.IsObs) {k j : ℕ}
    (hkj : k + j ≤ Nh) :
    ∏ i ∈ range j, ‖1 - frakN2F P' (histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (histVF2 (R.withMsq m) P' k o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) k (k + i)‖ ≤
      Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ)))) *
        ∏ i ∈ range j, ‖1 - nn2 R P' V m b μ₀ (k + i)‖ := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨-, hT, hBg⟩ := M.tadD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD
  obtain ⟨-, -, q, -, -, hloop⟩ := M.loopD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P' V
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
/-- **The coupling at `j` against the one at `N_h`** along `D_ε`:
`|β^{P'}_j| ≤ e^{c}(8/7)^{N_h−j}|β^{P'}_{N_h}|`. -/
theorem cw4_beta_up (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P' : ObsPts 2 L N) (V : OCoup .two) (hmu : OCoup2.mua V ≠ 0) {j : ℕ} (hj : j ≤ Nh) :
    ‖bt2 R P' V m b μ₀ j‖ ≤ Real.exp (2 * (M.core.cRel * (4 / betaL L) * M.core.ε)) *
      (8 / 7 : ℝ) ^ (Nh - j) * ‖bt2 R P' V m b μ₀ Nh‖ := by
  set n := Nh - j with hnd
  have hjn : j + n = Nh := by omega
  have hr := M.cw2_ratioD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P' V hmu
    (k := j) (j := n) (by omega)
  rw [hjn] at hr
  obtain ⟨-, -, hl⟩ := M.loopD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD P' V
  obtain ⟨q, -, -, hl⟩ := hl
  have hprod : (7 / 8 : ℝ) ^ n ≤ ∏ i ∈ range n, ‖1 - nn2 R P' V m b μ₀ (j + i)‖ := by
    have e : (7 / 8 : ℝ) ^ n = ∏ _i ∈ range n, (7 / 8 : ℝ) := by rw [prod_const, card_range]
    rw [e]
    refine prod_le_prod (fun _ _ => by norm_num) fun i hi => ?_
    have h1 := (hl (j + i) (by have := mem_range.1 hi; omega)).1
    have h2 := norm_sub_norm_le (1 : ℂ) (nn2 R P' V m b μ₀ (j + i))
    rw [norm_one] at h2
    linarith
  set c := 2 * (M.core.cRel * (4 / betaL L) * M.core.ε) with hcd
  set βj := ‖bt2 R P' V m b μ₀ j‖ with hβjd
  set βN := ‖bt2 R P' V m b μ₀ Nh‖ with hβNd
  have hβj0 : 0 ≤ βj := norm_nonneg _
  have h1 : Real.exp (-c) * βj * (7 / 8) ^ n ≤ βN :=
    le_trans (mul_le_mul_of_nonneg_left hprod (by positivity)) hr
  have h2 : βj = Real.exp c * (8 / 7) ^ n * (Real.exp (-c) * βj * (7 / 8) ^ n) := by
    have e1 : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
    have e2 : ((8 : ℝ) / 7) ^ n * (7 / 8) ^ n = 1 := by rw [← mul_pow]; norm_num
    calc βj = (Real.exp c * Real.exp (-c)) * (((8 : ℝ) / 7) ^ n * (7 / 8) ^ n) * βj := by
          rw [e1, e2]; ring
      _ = _ := by ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

set_option maxHeartbeats 4000000 in
/-- **The relative restart size along `D_ε`**:
`σ/|β_{a,N_h}| ≤ cw4Cmp(N_h − j_y)·M₀/|β^{(0,y)}_{m_r}|`. -/
theorem cw4_sig_cmp (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (y : Lam 2 L N) {mr : ℕ} (δ : ObsSt .two L N) (h0 : δ.IsObs)
    (hmy : mr ≤ Obs.coal L (0 : Lam 2 L N) y) (hj : Obs.coal L (0 : Lam 2 L N) y ≤ Nh)
    (hNh1 : 1 ≤ Nh) {M₀ : ℝ} (hM0 : 0 ≤ M₀) :
    cw2Sig R m b Nh y mr δ M₀ / ‖hBeta R m b (b - m) y Nh‖ ≤
      cw4Cmp M (Nh - Obs.coal L (0 : Lam 2 L N) y) *
        (M₀ / ‖bt2 R (ptsX y) (zV0 b) m b (b - m) mr‖) := by
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) with htd
  set jy := Obs.coal L (0 : Lam 2 L N) y with hjyd
  set n := Nh - jy with hnd
  set d := jy - mr with hdd
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb0
  have hNh0 : 0 < Nh := by omega
  have hβs := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD (ptsX y)
    (zV0 b) rfl hmu hNh0 mr (by omega)).1
  have hβN := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD (ptsX y)
    (zV0 b) rfl hmu hNh0 Nh le_rfl).1
  have hhB : ‖hBeta R m b (b - m) y Nh‖ = ‖bt2 R (ptsX y) (zV0 b) m b (b - m) Nh‖ := by
    rw [hBeta_eq_zV0 R m b (b - m) y hNh1]; rfl
  rw [hhB]
  -- the three comparisons
  have hpc := M.cw4_prod_cmpD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD (ptsX y)
    (zV0 b) δ h0 (k := mr) (j := d) (by omega)
  have hra := M.cw2_ratioD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD (ptsX y) (zV0 b)
    hmu (k := mr) (j := d) (by omega)
  rw [show mr + d = jy by omega] at hra
  have hup := M.cw4_beta_up N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD (ptsX y) (zV0 b)
    hmu (j := jy) hj
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id M.core.hC2
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8'
  have hs := cw2_histS_le_pow (R.withMsq m) hρ0 hρ8 t jy n
  rw [show jy + n = Nh by omega] at hs
  have hsj := histS_pos' (R.withMsq m) hρ0 hρ8 t jy
  have hsN := histS_pos' (R.withMsq m) hρ0 hρ8 t Nh
  have hsq : histS (R.withMsq m) jy t ^ 2 / histS (R.withMsq m) Nh t ^ 2 ≤
      (15 / 14 : ℝ) ^ (2 * n) := by
    rw [div_le_iff₀ (by positivity), pow_mul, show ((15 / 14 : ℝ) ^ 2) ^ n =
      ((15 / 14 : ℝ) ^ n) ^ 2 by rw [← pow_mul, ← pow_mul, mul_comm], ← mul_pow]
    exact pow_le_pow_left₀ hsj.le hs 2
  -- assemble
  set Pf := ∏ i ∈ range d, ‖1 - frakN2F (ptsX y) (histCovO (R.withMsq m) t)
    (histVF2 (R.withMsq m) (ptsX y) mr δ t) mr (mr + i)‖ with hPf
  set Pn := ∏ i ∈ range d, ‖1 - nn2 R (ptsX y) (zV0 b) m b (b - m) (mr + i)‖ with hPn
  set Cm := Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ))))
  set c := 2 * (M.core.cRel * (4 / betaL L) * M.core.ε)
  set βs := ‖bt2 R (ptsX y) (zV0 b) m b (b - m) mr‖
  set βj := ‖bt2 R (ptsX y) (zV0 b) m b (b - m) jy‖
  set βN := ‖bt2 R (ptsX y) (zV0 b) m b (b - m) Nh‖
  have hσ : cw2Sig R m b Nh y mr δ M₀ =
      histS (R.withMsq m) jy t ^ 2 / histS (R.withMsq m) Nh t ^ 2 * (M₀ * Pf) := by
    rw [show cw2Sig R m b Nh y mr δ M₀ = histS (R.withMsq m) jy t ^ 2 * (M₀ * Pf) /
      histS (R.withMsq m) Nh t ^ 2 from rfl]; ring
  rw [hσ]
  have hPf0 : 0 ≤ Pf := prod_nonneg fun _ _ => norm_nonneg _
  have hPn0 : 0 ≤ Pn := prod_nonneg fun _ _ => norm_nonneg _
  have hec : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
  -- `βs·Pn ≤ e^c βj`
  have hPi : βs * Pn ≤ Real.exp c * βj := by
    have := mul_le_mul_of_nonneg_left hra (Real.exp_pos c).le
    calc βs * Pn = Real.exp c * (Real.exp (-c) * βs * Pn) := by
          rw [← mul_assoc, ← mul_assoc, hec, one_mul]
      _ ≤ _ := this
  have hkey : M₀ * Pf * βs ≤ M₀ * (Cm * (Real.exp c * (Real.exp c * (8 / 7) ^ n * βN))) := by
    have h1 : Pf * βs ≤ Cm * (βs * Pn) :=
      calc Pf * βs ≤ Cm * Pn * βs := mul_le_mul_of_nonneg_right hpc hβs.le
        _ = Cm * (βs * Pn) := by ring
    have h2 : Cm * (βs * Pn) ≤ Cm * (Real.exp c * (Real.exp c * (8 / 7) ^ n * βN)) :=
      mul_le_mul_of_nonneg_left (hPi.trans (mul_le_mul_of_nonneg_left hup (Real.exp_pos c).le))
        (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left (h1.trans h2) hM0
    linarith [show M₀ * (Pf * βs) = M₀ * Pf * βs by ring]
  have hq : M₀ * Pf / βN ≤ Cm * Real.exp c ^ 2 * (8 / 7) ^ n * (M₀ / βs) := by
    rw [div_le_iff₀ hβN, show Cm * Real.exp c ^ 2 * (8 / 7) ^ n * (M₀ / βs) * βN =
      Cm * Real.exp c ^ 2 * (8 / 7) ^ n * M₀ * βN / βs by ring, le_div_iff₀ hβs]
    exact hkey.trans (le_of_eq (by ring))
  have hq0 : 0 ≤ M₀ * Pf / βN := div_nonneg (mul_nonneg hM0 hPf0) hβN.le
  calc histS (R.withMsq m) jy t ^ 2 / histS (R.withMsq m) Nh t ^ 2 * (M₀ * Pf) / βN
      = histS (R.withMsq m) jy t ^ 2 / histS (R.withMsq m) Nh t ^ 2 * (M₀ * Pf / βN) := by ring
    _ ≤ (15 / 14 : ℝ) ^ (2 * n) * (Cm * Real.exp c ^ 2 * (8 / 7) ^ n * (M₀ / βs)) :=
        mul_le_mul hsq hq hq0 (pow_nonneg (by norm_num) _)
    _ = cw4Cmp M n * (M₀ / βs) := by unfold cw4Cmp; ring

set_option maxHeartbeats 4000000 in
/-- **The relative restart size of the pair-difference datum**:
`σ/|β_{a,N_h}| ≤ cw4Cmp(N_h − j_y)·cddRel(K_p, ǧ_{ms}, a_{ms}, rpIota 0 0, A, r)`
(the envelope `M₀ = cddM` of `pl4_T6_inputs`). -/
theorem cw4_sig_rel (N : ℕ) (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m) (hmL : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (x y : Lam 2 L N) {ms r : ℕ} (hk0 : 0 < ms) (hmx : ms < Obs.coal L (0 : Lam 2 L N) x)
    (hmy : ms < Obs.coal L (0 : Lam 2 L N) y) (hj : Obs.coal L (0 : Lam 2 L N) y ≤ Nh)
    (hrk : r ≤ ms) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hdist : supNorm (y - x) ≤ L ^ (ms - r))
    (hs0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms))
    (hs : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) ≤ 1 / 2)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 3) ≤ 1) :
    cw2Sig R m b Nh y ms (pl2Delta R m b (b - m) x y ms)
        (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0)
          (R.withMsq m).A r) / ‖hBeta R m b (b - m) y Nh‖ ≤
      cw4Cmp M (Nh - Obs.coal L (0 : Lam 2 L N) y) *
        M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
          (R.withMsq m).A r := by
  obtain ⟨-, h0, -, -, -, -, -, -, kk, ww, -, -, hM0, -, -, -, -, hrel⟩ :=
    M.pl4_T6_inputs N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b hD hspl hm0 hmL x y hk0 hmx hmy hj
      hrk hblk hdist hs0 hs hreg
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hβs := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD (ptsX y)
    (zV0 b) rfl (zV_mua_ne hb0) (by omega) ms (by omega)).1
  refine (M.cw4_sig_cmp N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b hD y _ h0 hmy.le hj (by omega)
    hM0.le).trans (mul_le_mul_of_nonneg_left ?_ (cw4Cmp_pos M _).le)
  rw [div_le_iff₀ hβs]
  exact hrel

end MasterFacts

end

end Spin2
