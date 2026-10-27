import Spin2.Pair.PairVStep1

/-!
# `PairUnitSeed` from the spin facts of the master construction

**`pairUnitSeed_MF (M : MasterFacts L)`**: along every admissible trajectory, for every `λ` with
(H_λ) and the smallness `max(K_M(K_λ), 0)ǧ_j ≤ 1/2` (the hypotheses of `thm_pairAbove_red_joint`),
`PairUnitSeed c_u` holds with
`c_u = pairUnitC = (81/16)ℓ²e^{K_Z}(1 + 3K_p)`, `K_p = max(lamRelK(β_L, c_g, B₁+B₂+B₃, B', c_q, c_δ, e_R, 4), 0)`
(independent of `λ`, `K_λ`, the trajectory and `x`).

Proof (`j = j_x = n + 1`, `u = (ǧ_n/b)^{1/3}`, `v = (ǧ_j/b)^{1/3}`):
* `s_j² = ℓ²/|Z_j| ≤ ℓ²e^{K_Z}u` (the `log|Z|` bound of `SpinConcl`, `ǧ_n ≤ 1`);
* `|β^{mir}_{a,j}| ≤ (81/64)|β^{mir}_{a,n}|` (exact flow `bt2_flow`, `Case2Rel`, `‖𝔫‖ ≤ 1/8`) and
  `|β^{mir}_{a,n}| = b|λ̂^{mir}_n| ≤ b(1 + 3K_p)u` ((H_λ) for `λ̂^{mir} = μ_a/μ_{a,0}` at `ptsS x`,
  vertex `zV0 b`, from `LamConcl` via `hLam_case2`, `RelConcl2G`, `LoopConcl`; `ǧ + a ≤ 3`);
* `‖M_j‖ǧ_j ≥ (1/2)(b/ǧ_j)^{1/3}ǧ_j = (1/2)bv²` (`MagConcl` + smallness) and `u ≤ v` (`GMonoConcl`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

/-- The constant `K_p` of (H_λ) for the pair/mirror vertices under `MasterFacts`. -/
def MasterFacts.Kp {L : ℕ} [NeZero L] (M : MasterFacts L) : ℝ :=
  max (lamRelK (betaL L) M.core.cg (M.core.B₁ + M.core.B₂ + M.core.B₃) M.core.B' M.core.cq
    M.core.cRel (eRange (betaL L) M.core.Ke 1) 4) 0

/-- The constant of `PairUnitSeed`. -/
def pairUnitC {L : ℕ} [NeZero L] (M : MasterFacts L) : ℝ :=
  81 / 16 * M.core.ℓ ^ 2 * Real.exp M.core.KZ * (1 + 3 * M.Kp)

theorem MasterFacts.Kp_nonneg {L : ℕ} [NeZero L] (M : MasterFacts L) : 0 ≤ M.Kp := le_max_right _ _

theorem pairUnitC_nonneg {L : ℕ} [NeZero L] (M : MasterFacts L) : 0 ≤ pairUnitC M := by
  unfold pairUnitC
  have := M.Kp_nonneg
  have := Real.exp_pos M.core.KZ
  positivity

theorem zV0_mua_ne {b : ℝ} (hb : 0 < b) : Obs2.OCoup2.mua (zV0 b) ≠ 0 := by
  show -(b : ℂ) ≠ 0
  rw [neg_ne_zero]; exact_mod_cast hb.ne'

/-- `(b/g)^{1/3}g = b((g/b)^{1/3})²`. -/
theorem rpow_third_mul {b g : ℝ} (hb : 0 < b) (hg : 0 < g) :
    (b / g) ^ (1 / 3 : ℝ) * g = b * ((g / b) ^ (1 / 3 : ℝ)) ^ 2 := by
  set v := (g / b) ^ (1 / 3 : ℝ) with hv
  have hv0 : 0 < v := Real.rpow_pos_of_pos (div_pos hg hb) _
  have h1 : (b / g) ^ (1 / 3 : ℝ) = v⁻¹ := by
    rw [hv, ← Real.inv_rpow (div_pos hg hb).le, inv_div]
  have h3 : v ^ 3 = g / b := by
    rw [hv, one_div]
    exact Real.rpow_inv_natCast_pow (div_pos hg hb).le (by norm_num)
  have hg' : g = b * v ^ 3 := by rw [h3]; field_simp
  rw [h1, hg']
  field_simp

set_option maxHeartbeats 4000000 in
/-- **`PairUnitSeed` under `MasterFacts`** (see the module docstring). -/
theorem pairUnitSeed_MFD {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (lam : ℕ → ℂ) (Kl : ℝ) (hKl : 0 ≤ Kl) (hl : HLam R Nh m b μ₀ lam Kl)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) :
    PairUnitSeed R Nh m b μ₀ lam (pairUnitC M) := by
  intro x _ hj1 hjN
  have hL49 := M.core.hL49
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  set g : ℕ → ℝ := fun k => (t k).1 with hgd
  obtain ⟨n, hn⟩ : ∃ n, Obs.coal L (0 : Lam 2 L N) x = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hj1).symm⟩
  rw [hn] at hjN
  have hnN : n < Nh := by omega
  have hgpos : ∀ k ≤ Nh, 0 < g k := fun k hk => (hD k hk).1
  have hg1 : ∀ k ≤ Nh, g k ≤ 1 := fun k hk => ((hD k hk).2.1).trans M.eps_le
  have hmn : ∀ k ≤ Nh, m * ((L : ℝ) ^ k) ^ 2 ≤ 1 := fun k hk => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hzA : zA L m n ≤ 2 := zA_le_two (by linarith only [hL2]) (hmn (n + 1) (by omega))
  have hzA0 := zA_nonneg L hm.1.le n
  set u := (g n / b) ^ (1 / 3 : ℝ) with hu
  set v := (g (n + 1) / b) ^ (1 / 3 : ℝ) with hv
  have hu0 : 0 ≤ u := Real.rpow_nonneg (div_pos (hgpos n hnN.le) hb).le _
  have huv : u ≤ v := by
    refine Real.rpow_le_rpow (div_pos (hgpos n hnN.le) hb).le ?_ (by norm_num)
    exact div_le_div_of_nonneg_right
      (M.gmonoD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD n hnN) hb.le
  -- (A) the field strength
  obtain ⟨-, -, -, -, hZ, -⟩ :=
    M.spinD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)
  obtain ⟨hZ0, hZb⟩ := hZ m hm b μ₀ hD n hnN.le
  set Z := (rawHist (R.withMsq m) (n + 1) t).Z with hZd
  have hZpos : 0 < ‖Z‖ := norm_pos_iff.2 hZ0
  have hZinv : ‖Z‖⁻¹ ≤ u * Real.exp M.core.KZ := by
    have hKZg : M.core.KZ * g n ≤ M.core.KZ :=
      mul_le_of_le_one_right M.KZ_nonneg (hg1 n hnN.le)
    have h1 : -Real.log ‖Z‖ ≤ Real.log (g n / b) * (1 / 3) + M.core.KZ := by
      have hZb' : |Real.log ‖Z‖ + 1 / 3 * Real.log (g n / b)| ≤ M.core.KZ * g n := hZb
      have := (abs_le.1 hZb').1
      linarith
    rw [← Real.exp_log hZpos, ← Real.exp_neg, hu,
      Real.rpow_def_of_pos (div_pos (hgpos n hnN.le) hb), ← Real.exp_add]
    exact Real.exp_le_exp.2 h1
  -- (B) the mirror coupling over one step
  have hmu := zV0_mua_ne hb
  obtain ⟨hB0, -, hloop⟩ := M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsS x) (zV0 b)
  have hrel := M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsS x) (zV0 b) hmu
  set bt := bt2 R (ptsS x) (zV0 b) m b μ₀ with hbtd
  have hstep : ‖bt (n + 1)‖ ≤ 81 / 64 * ‖bt n‖ := by
    obtain ⟨q, -, -, hl'⟩ := hloop
    have hnn := (hl' n hnN).1
    have hfl := bt2_flow R (ptsS x) (zV0 b) (by omega : Nh < N) m b μ₀ hnN
    obtain ⟨he, hsm⟩ := hrel n hnN
    have h1n : ‖1 - nn2 R (ptsS x) (zV0 b) m b μ₀ n‖ ≤ 9 / 8 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]; linarith
    have hprod : ‖bt n * (1 - nn2 R (ptsS x) (zV0 b) m b μ₀ n)‖ ≤ 9 / 8 * ‖bt n‖ := by
      rw [norm_mul]
      calc ‖bt n‖ * ‖1 - nn2 R (ptsS x) (zV0 b) m b μ₀ n‖ ≤ ‖bt n‖ * (9 / 8) :=
            mul_le_mul_of_nonneg_left h1n (norm_nonneg _)
        _ = 9 / 8 * ‖bt n‖ := by ring
    rw [show bt (n + 1) = _ from hfl]
    refine (norm_sub_le _ _).trans ?_
    have h2 : ‖err2 R (ptsS x) (zV0 b) m b μ₀ n‖ ≤
        1 / 8 * ‖bt n * (1 - nn2 R (ptsS x) (zV0 b) m b μ₀ n)‖ :=
      he.trans (mul_le_mul_of_nonneg_right hsm (norm_nonneg _))
    nlinarith [norm_nonneg (bt n * (1 - nn2 R (ptsS x) (zV0 b) m b μ₀ n))]
  -- (C) (H_λ) for the mirror vertex
  have hLC := M.lamD
  have hLm : HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV0 b) m b μ₀) M.Kp := by
    have h := hLam_case2D hLC hP hi0 hRℓ hRA hRρ (by omega) hm hD hB0 M.cRel_nonneg hmu hrel hloop
    exact hLam_mono hb hm.1.le (fun k hk => (hD k hk.le).1) h (le_max_left _ _)
  have hbt0 : ‖bt 0‖ = b := by
    rw [hbtd, bt2_zero]
    show ‖-(-(b : ℂ))‖ = b
    rw [neg_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
  have hbtn : ‖bt n‖ ≤ b * ((1 + 3 * M.Kp) * u) := by
    have h := hLm n hnN
    have hlam : ‖lamHat2 R (ptsS x) (zV0 b) m b μ₀ n‖ ≤ (1 + 3 * M.Kp) * u := by
      have e1 : ‖lamHat2 R (ptsS x) (zV0 b) m b μ₀ n‖ ≤ u + M.Kp * u * (g n + zA L m n) := by
        have := norm_le_insert' (lamHat2 R (ptsS x) (zV0 b) m b μ₀ n) ((u : ℝ) : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] at this
        linarith
      have e2 : M.Kp * u * (g n + zA L m n) ≤ M.Kp * u * 3 :=
        mul_le_mul_of_nonneg_left (by linarith [hg1 n hnN.le]) (mul_nonneg M.Kp_nonneg hu0)
      linarith
    have e : bt n = bt 0 * lamHat2 R (ptsS x) (zV0 b) m b μ₀ n := by
      have h0 : bt 0 ≠ 0 := by
        rw [hbtd, bt2_zero]; exact neg_ne_zero.2 hmu
      unfold lamHat2; rw [← hbtd]; field_simp
    rw [e, norm_mul, hbt0]
    exact mul_le_mul_of_nonneg_left hlam hb.le
  -- (D) the magnetisation
  have hMg := M.magD N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega) m hm b μ₀ hD lam Kl hKl hl
    (n + 1) hjN
  set w := (b / g (n + 1)) ^ (1 / 3 : ℝ) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg (div_pos hb (hgpos _ hjN)).le _
  have hMlow : w / 2 ≤ ‖Mmag R m b μ₀ lam (n + 1)‖ := by
    have hs := hsmall (n + 1) hjN
    have e1 : ‖Mmag R m b μ₀ lam (n + 1) - ((w : ℝ) : ℂ)‖ ≤ w / 2 := by
      refine hMg.trans ?_
      have : spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0 * g (n + 1) ≤ 1 / 2 :=
        le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hgpos _ hjN).le) hs
      calc spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0 * w * g (n + 1)
          = (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0 * g (n + 1)) * w := by ring
        _ ≤ 1 / 2 * w := mul_le_mul_of_nonneg_right this hw0
        _ = w / 2 := by ring
    have e2 := norm_sub_norm_le ((w : ℝ) : ℂ) (Mmag R m b μ₀ lam (n + 1))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0, norm_sub_rev] at e2
    linarith
  have hvB : b * v ^ 2 / 2 ≤ vwB R m b μ₀ lam x := by
    unfold vwB; rw [hn]
    have e := rpow_third_mul hb (hgpos _ hjN)
    rw [← hw] at e
    calc b * v ^ 2 / 2 = w / 2 * g (n + 1) := by rw [hv, ← e]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hMlow (hgpos _ hjN).le
  -- assembly
  have hS : histS (R.withMsq m) (n + 1) t ^ 2 = ‖Z‖⁻¹ * M.core.ℓ ^ 2 := by
    unfold histS; rw [mul_pow, Step2.fscale_sq, ← hRℓ]; rfl
  unfold pM
  rw [hn]
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
    _ ≤ pairUnitC M * vwB R m b μ₀ lam x :=
        mul_le_mul_of_nonneg_left hvB (pairUnitC_nonneg M)

/-- Corollary of `pairUnitSeed_MFD` (`Admissible` ⟹ the domain condition). -/
theorem pairUnitSeed_MF {L : ℕ} [NeZero L] (M : MasterFacts L)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (lam : ℕ → ℂ) (Kl : ℝ) (hKl : 0 ≤ Kl) (hl : HLam R Nh m b μ₀ lam Kl)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) :
    PairUnitSeed R Nh m b μ₀ lam (pairUnitC M)  :=
  pairUnitSeed_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm.1 lam Kl hKl hl hsmall

end

end Spin2
