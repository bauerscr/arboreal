import Spin2.Pair.PairUnit

/-!
# The absolute size of the `wM` weight `M_{a,k}`

The `ab` sizes of the joint induction are relative to the weights `M_{a,k} = 2s_k²|β_{a,k}|`
(`vwA`) and `M_b = ‖M_{j_x}‖ǧ_{j_x}` (`vwB`). The defects of `PairDefSumR` are absolute, of size
`‖M_{j_x}‖²ǧ_{j_x}`. The conversion is the following bound, the scale-`k` copy of
`pairUnitSeed_MFD` at the unmirrored points.

* **`pM_le_mag_MFD`**: along every trajectory in `D_ε`, for every pair of points `P`, under (H_λ)
  and `max(K_M(K_λ), 0)ǧ_j ≤ 1/2` (the hypotheses of `pairUnitSeed_MF`), for `1 ≤ j ≤ k ≤ N_h`:
  `2s_k²|β^P_{a,k}| ≤ c_u‖M_j‖ǧ_k`, with `c_u = pairUnitC M`.
* **`vwA_le_mag_MFD`**, **`vwA_le_mag_MF`**: `M_{a,k} ≤ c_u‖M_{j_x}‖ǧ_k` for `j_x ≤ k ≤ N_h`;
* **`hBeta_up`**, **`hBeta_up_MFD`**: `|β_{a,k+1}| ≤ (21/16)|β_{a,k}|` for `k ≤ N_h`.

Proof: `s_k² ≤ ℓ²e^{K_Z}u`, `|β_k| ≤ (81/64)b(1 + 3K_p)u` (`u = (ǧ_{k-1}/b)^{1/3}`) as in
`pairUnitSeed_MFD`, so `2s_k²|β_k| ≤ (81/32)ℓ²e^{K_Z}(1 + 3K_p)·bv_k²` with `v_k = (ǧ_k/b)^{1/3}`.
Then `bv_k² = (b/ǧ_k)^{1/3}ǧ_k ≤ (b/ǧ_j)^{1/3}ǧ_k ≤ 2‖M_j‖ǧ_k` (`GMonoConcl`, `MagConcl`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

set_option maxHeartbeats 4000000 in
/-- **`2s_k²|β^P_{a,k}| ≤ c_u‖M_j‖ǧ_k`** for `1 ≤ j ≤ k ≤ N_h` (see the module docstring). -/
theorem pM_le_mag_MFD {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (lam : ℕ → ℂ) (Kl : ℝ) (hKl : 0 ≤ Kl) (hl : HLam R Nh m b μ₀ lam Kl)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2)
    (P : Obs2.ObsPts 2 L N) {j k : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hkN : k ≤ Nh) :
    pM (R.withMsq m) P (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k ≤
      pairUnitC M * ‖Mmag R m b μ₀ lam j‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 := by
  have hL49 := M.core.hL49
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  set g : ℕ → ℝ := fun k => (t k).1 with hgd
  obtain ⟨n, hn⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  subst hn
  have hnN : n < Nh := by omega
  have hgpos : ∀ k ≤ Nh, 0 < g k := fun k hk => (hD k hk).1
  have hg1 : ∀ k ≤ Nh, g k ≤ 1 := fun k hk => ((hD k hk).2.1).trans M.eps_le
  have hmono1 := M.gmonoD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hgm : ∀ i l, i ≤ l → l ≤ Nh → g i ≤ g l := by
    intro i l hil hl'
    have key : ∀ d, i + d ≤ Nh → g i ≤ g (i + d) := by
      intro d
      induction d with
      | zero => intro _; exact le_rfl
      | succ d ih => intro hd; exact (ih (by omega)).trans (hmono1 (i + d) (by omega))
    have := key (l - i) (by omega)
    rwa [show i + (l - i) = l by omega] at this
  set u := (g n / b) ^ (1 / 3 : ℝ) with hu
  set v := (g (n + 1) / b) ^ (1 / 3 : ℝ) with hv
  have hu0 : 0 ≤ u := Real.rpow_nonneg (div_pos (hgpos n hnN.le) hb).le _
  have huv : u ≤ v := by
    refine Real.rpow_le_rpow (div_pos (hgpos n hnN.le) hb).le ?_ (by norm_num)
    exact div_le_div_of_nonneg_right (hmono1 n hnN) hb.le
  -- (A) the field strength
  obtain ⟨-, -, -, -, hZ, -⟩ :=
    M.spinD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)
  obtain ⟨hZ0, hZb⟩ := hZ m hm b μ₀ hD n hnN.le
  set Z := (rawHist (R.withMsq m) (n + 1) t).Z with hZd
  have hZpos : 0 < ‖Z‖ := norm_pos_iff.2 hZ0
  have hZinv : ‖Z‖⁻¹ ≤ u * Real.exp M.core.KZ := by
    have h1 : -Real.log ‖Z‖ ≤ Real.log (g n / b) * (1 / 3) + M.core.KZ := by
      have hKZg : M.core.KZ * g n ≤ M.core.KZ :=
        mul_le_of_le_one_right M.KZ_nonneg (hg1 n hnN.le)
      have hZb' : |Real.log ‖Z‖ + 1 / 3 * Real.log (g n / b)| ≤ M.core.KZ * g n := hZb
      have := (abs_le.1 hZb').1
      linarith
    rw [← Real.exp_log hZpos, ← Real.exp_neg, hu,
      Real.rpow_def_of_pos (div_pos (hgpos n hnN.le) hb), ← Real.exp_add]
    exact Real.exp_le_exp.2 h1
  -- (B) the coupling over one step
  have hmu := zV0_mua_ne hb
  obtain ⟨hB0, -, hloop⟩ := M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV0 b)
  have hrel := M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV0 b) hmu
  set bt := bt2 R P (zV0 b) m b μ₀ with hbtd
  have hstep : ‖bt (n + 1)‖ ≤ 81 / 64 * ‖bt n‖ := by
    obtain ⟨q, -, -, hl'⟩ := hloop
    have hnn := (hl' n hnN).1
    have hfl := bt2_flow R P (zV0 b) (by omega : Nh < N) m b μ₀ hnN
    obtain ⟨he, hsm⟩ := hrel n hnN
    have h1n : ‖1 - nn2 R P (zV0 b) m b μ₀ n‖ ≤ 9 / 8 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]; linarith
    have hprod : ‖bt n * (1 - nn2 R P (zV0 b) m b μ₀ n)‖ ≤ 9 / 8 * ‖bt n‖ := by
      rw [norm_mul]
      calc ‖bt n‖ * ‖1 - nn2 R P (zV0 b) m b μ₀ n‖ ≤ ‖bt n‖ * (9 / 8) :=
            mul_le_mul_of_nonneg_left h1n (norm_nonneg _)
        _ = 9 / 8 * ‖bt n‖ := by ring
    rw [show bt (n + 1) = _ from hfl]
    refine (norm_sub_le _ _).trans ?_
    have h2 : ‖err2 R P (zV0 b) m b μ₀ n‖ ≤
        1 / 8 * ‖bt n * (1 - nn2 R P (zV0 b) m b μ₀ n)‖ :=
      he.trans (mul_le_mul_of_nonneg_right hsm (norm_nonneg _))
    nlinarith [norm_nonneg (bt n * (1 - nn2 R P (zV0 b) m b μ₀ n))]
  -- (C) (H_λ) for the vertex `zV0 b` at `P`
  have hLC := M.lamD
  have hLm : HLam R Nh m b μ₀ (lamHat2 R P (zV0 b) m b μ₀) M.Kp := by
    have h := hLam_case2D hLC hP hi0 hRℓ hRA hRρ (by omega) hm hD hB0 M.cRel_nonneg hmu hrel hloop
    exact hLam_mono hb hm.1.le (fun k hk => (hD k hk.le).1) h (le_max_left _ _)
  have hbt0 : ‖bt 0‖ = b := by
    rw [hbtd, bt2_zero]
    show ‖-(-(b : ℂ))‖ = b
    rw [neg_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
  have hmn : ∀ k ≤ Nh, m * ((L : ℝ) ^ k) ^ 2 ≤ 1 := fun k hk => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hzA : zA L m n ≤ 2 := zA_le_two (by linarith only [hL2]) (hmn (n + 1) (by omega))
  have hbtn : ‖bt n‖ ≤ b * ((1 + 3 * M.Kp) * u) := by
    have h := hLm n hnN
    have hlam : ‖lamHat2 R P (zV0 b) m b μ₀ n‖ ≤ (1 + 3 * M.Kp) * u := by
      have e1 : ‖lamHat2 R P (zV0 b) m b μ₀ n‖ ≤ u + M.Kp * u * (g n + zA L m n) := by
        have := norm_le_insert' (lamHat2 R P (zV0 b) m b μ₀ n) ((u : ℝ) : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] at this
        linarith
      have e2 : M.Kp * u * (g n + zA L m n) ≤ M.Kp * u * 3 :=
        mul_le_mul_of_nonneg_left (by linarith [hg1 n hnN.le]) (mul_nonneg M.Kp_nonneg hu0)
      linarith
    have e : bt n = bt 0 * lamHat2 R P (zV0 b) m b μ₀ n := by
      have h0 : bt 0 ≠ 0 := by
        rw [hbtd, bt2_zero]; exact neg_ne_zero.2 hmu
      unfold lamHat2; rw [← hbtd]; field_simp
    rw [e, norm_mul, hbt0]
    exact mul_le_mul_of_nonneg_left hlam hb.le
  -- (D) the magnetisation at `j`
  have hjN : j ≤ Nh := by omega
  have hMg := M.magD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega) m hm b μ₀ hD lam Kl hKl hl
    j hjN
  set w := (b / g j) ^ (1 / 3 : ℝ) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg (div_pos hb (hgpos _ hjN)).le _
  have hMlow : w / 2 ≤ ‖Mmag R m b μ₀ lam j‖ := by
    have hs := hsmall j hjN
    have e1 : ‖Mmag R m b μ₀ lam j - ((w : ℝ) : ℂ)‖ ≤ w / 2 := by
      refine hMg.trans ?_
      have : spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0 * g j ≤ 1 / 2 :=
        le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hgpos _ hjN).le) hs
      calc spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0 * w * g j
          = (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0 * g j) * w := by ring
        _ ≤ 1 / 2 * w := mul_le_mul_of_nonneg_right this hw0
        _ = w / 2 := by ring
    have e2 := norm_sub_norm_le ((w : ℝ) : ℂ) (Mmag R m b μ₀ lam j)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0, norm_sub_rev] at e2
    linarith
  -- `b v² = (b/ǧ_k)^{1/3}ǧ_k ≤ (b/ǧ_j)^{1/3}ǧ_k`
  have hgk := hgpos (n + 1) hkN
  have hvB : b * v ^ 2 / 2 ≤ ‖Mmag R m b μ₀ lam j‖ * g (n + 1) := by
    have e := rpow_third_mul hb hgk
    have hwk : (b / g (n + 1)) ^ (1 / 3 : ℝ) ≤ w := by
      refine Real.rpow_le_rpow (div_pos hb hgk).le ?_ (by norm_num)
      exact div_le_div_of_nonneg_left hb.le (hgpos _ hjN) (hgm j (n + 1) hjk hkN)
    calc b * v ^ 2 / 2 = (b / g (n + 1)) ^ (1 / 3 : ℝ) * g (n + 1) / 2 := by rw [hv, ← e]
      _ ≤ w * g (n + 1) / 2 := by gcongr
      _ = w / 2 * g (n + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hMlow hgk.le
  -- assembly
  have hS : histS (R.withMsq m) (n + 1) t ^ 2 = ‖Z‖⁻¹ * M.core.ℓ ^ 2 := by
    unfold histS; rw [mul_pow, Step2.fscale_sq, ← hRℓ]; rfl
  unfold pM
  change 2 * histS (R.withMsq m) (n + 1) t ^ 2 * ‖bt (n + 1)‖ ≤ _
  rw [hS]
  have hK3 : 0 ≤ 1 + 3 * M.Kp := by have := M.Kp_nonneg; linarith
  have hl2 : 0 ≤ M.core.ℓ ^ 2 := sq_nonneg _
  have hE := Real.exp_pos M.core.KZ
  have hbt1 : ‖bt (n + 1)‖ ≤ 81 / 64 * (b * ((1 + 3 * M.Kp) * u)) :=
    hstep.trans (mul_le_mul_of_nonneg_left hbtn (by norm_num))
  have huu : u * u ≤ v ^ 2 := by rw [sq]; exact mul_le_mul huv huv hu0 (hu0.trans huv)
  calc 2 * (‖Z‖⁻¹ * M.core.ℓ ^ 2) * ‖bt (n + 1)‖
      ≤ 2 * (u * Real.exp M.core.KZ * M.core.ℓ ^ 2) * (81 / 64 * (b * ((1 + 3 * M.Kp) * u))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hZinv hl2) (by norm_num)) hbt1 (norm_nonneg _) ?_
        positivity
    _ = 81 / 32 * M.core.ℓ ^ 2 * Real.exp M.core.KZ * (1 + 3 * M.Kp) * b * (u * u) := by ring
    _ ≤ 81 / 32 * M.core.ℓ ^ 2 * Real.exp M.core.KZ * (1 + 3 * M.Kp) * b * v ^ 2 :=
        mul_le_mul_of_nonneg_left huu (by positivity)
    _ = pairUnitC M * (b * v ^ 2 / 2) := by unfold pairUnitC; ring
    _ ≤ pairUnitC M * (‖Mmag R m b μ₀ lam j‖ * g (n + 1)) :=
        mul_le_mul_of_nonneg_left hvB (pairUnitC_nonneg M)
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- **`M_{a,k} ≤ c_u‖M_{j_x}‖ǧ_k`** for `j_x ≤ k ≤ N_h`, along trajectories in `D_ε`. -/
theorem vwA_le_mag_MFD {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (lam : ℕ → ℂ) (Kl : ℝ) (hKl : 0 ≤ Kl) (hl : HLam R Nh m b μ₀ lam Kl)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2)
    (x : Lam 2 L N) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x) {k : ℕ}
    (hjk : Obs.coal L (0 : Lam 2 L N) x ≤ k) (hkN : k ≤ Nh)
    (hβ : hBeta R m b μ₀ x k ≠ 0) :
    vwA R m b μ₀ x k ≤ pairUnitC M * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 := by
  have h := pM_le_mag_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam Kl hKl hl hsmall
    (ptsX x) h1 hjk hkN
  have e : vwA R m b μ₀ x k = pM (R.withMsq m) (ptsX x) (zV0 b)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k := by
    unfold vwA; rw [if_neg hβ, hBeta_eq_zV0 R m b μ₀ x (h1.trans hjk)]; rfl
  rw [e]; exact h

/-- `vwA_le_mag_MFD` along admissible trajectories. -/
theorem vwA_le_mag_MF {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (lam : ℕ → ℂ) (Kl : ℝ) (hKl : 0 ≤ Kl) (hl : HLam R Nh m b μ₀ lam Kl)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2)
    (x : Lam 2 L N) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x) {k : ℕ}
    (hjk : Obs.coal L (0 : Lam 2 L N) x ≤ k) (hkN : k ≤ Nh)
    (hβ : hBeta R m b μ₀ x k ≠ 0) :
    vwA R m b μ₀ x k ≤ pairUnitC M * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 :=
  vwA_le_mag_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm.1 lam Kl hKl hl hsmall x h1
    hjk hkN hβ

/-- **The upward ratio**: `|β_{a,k+1}| ≤ (21/16)|β_{a,k}|` for `k ≤ N_h` (from `hBeta_rel_of`:
`β' = (1 − 𝔫)β − err`, `‖𝔫‖ ≤ 1/8`, `‖err‖ ≤ |β'|/7`). -/
theorem hBeta_up {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {Nh : ℕ} (hN : Nh + 2 = N) {m b μ₀ cδ : ℝ} (hb : 0 < b) (x : Lam 2 L N)
    (hrel : Case2Rel R (ptsX x) (zV b) Nh m b μ₀ cδ)
    (hn : ∀ k < Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤ 1 / 8)
    (htop : Case2TopStep R (ptsX x) (zV b) Nh m b μ₀) :
    ∀ k ≤ Nh, ‖hBeta R m b μ₀ x (k + 1)‖ ≤ 21 / 16 * ‖hBeta R m b μ₀ x k‖ := by
  intro k hk
  obtain ⟨-, -, hfl, herr⟩ := hBeta_rel_of R hN hb x hrel hn htop k hk
  set β := hBeta R m b μ₀ x k
  set β' := hBeta R m b μ₀ x (k + 1)
  set n := nn2 R (ptsX x) (zV b) m b μ₀ k
  set e := err2 R (ptsX x) (zV b) m b μ₀ k
  have hnk : ‖n‖ ≤ 1 / 8 := by
    rcases Nat.lt_or_ge k Nh with h | h
    · exact hn k h
    · obtain rfl : k = Nh := by omega
      exact htop.1
  have hu : (if k < Nh then 8 / 7 * (cδ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2)
      else (1 / 7 : ℝ)) ≤ 1 / 7 := by
    split_ifs with h
    · have := (hrel k h).2; linarith
    · exact le_rfl
  have he : ‖e‖ ≤ 1 / 7 * ‖β'‖ := herr.trans (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
  have h1n : ‖1 - n‖ ≤ 9 / 8 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]; linarith
  have h2 : ‖β'‖ ≤ 9 / 8 * ‖β‖ + ‖e‖ := by
    rw [hfl]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_right h1n (norm_nonneg β)
    linarith
  linarith

/-- `hBeta_up` along trajectories in `D_ε`. -/
theorem hBeta_up_MFD {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x : Lam 2 L N) :
    ∀ k ≤ Nh, ‖hBeta R m b μ₀ x (k + 1)‖ ≤ 21 / 16 * ‖hBeta R m b μ₀ x k‖ := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨q, -, -, hl⟩ :=
    (M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (zV b)).2.2
  exact hBeta_up R hNh hb x
    (M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (zV b) (zV_mua_ne hb))
    (fun k hk => (hl k hk).1)
    (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x)).1

end

end Spin2
