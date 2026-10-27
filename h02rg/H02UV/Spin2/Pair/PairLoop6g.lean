import Spin2.Pair.PairLoop6f

/-!
# The constant loop, per scale (7): the first summability condition discharged (task 2)

* **`pl6_sum_le`**: along every admissible trajectory, for every `x` and path `w`, the first
  summability condition of `pairJointSizesP3_of_VS` holds with
  `c_e = pl6ce = 2C_Ek₀ + Θm̄`, `Θ = pl6Θ = C_E(6c²G₂ + 2cε) + C_Ncε`, `G₂ = 4ε/β_L + ε²`
  (`pl6_item_le` summed with `pairLoop2_sum_le`; `∑_{j≤k≤N_h}ǧ_k² ≤ G₂` by `sum_gsq_Ico_le`).
* **`pairJointSizesP3_closed`**: `pairJointSizesP3_of_VS` with the first summability condition
  discharged under the two `ε`-requirements
  `C₁k(2 + 2·8c_x + 1)·cε ≤ 1/72` and `(1 + c_W(L)cε)^{L²} ≤ 2` (and `0 ≤ c_u`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs2

/-- `G₂ = 4ε/β_L + ε²` (`∑_{j≤k≤N_h}ǧ_k² ≤ G₂`). -/
def pl6G2 (L : ℕ) (ε : ℝ) : ℝ := 4 * ε / betaL L + ε ^ 2

/-- **The loop factor** `Θ = C_E(6c²G₂ + 2cε) + C_N·cε`. -/
def pl6Θ {L : ℕ} [NeZero L] (M : MasterFacts L) (C₁k C₁w C₁w' Clo Clb : ℝ) : ℝ :=
  pl6CEM M C₁k C₁w C₁w' Clo Clb * (6 * M.core.c ^ 2 * pl6G2 L M.core.ε + 2 * M.core.c * M.core.ε) +
    pl6CNM L C₁w * (M.core.c * M.core.ε)

/-- **The summability constant** `c_e = 2C_Ek₀ + Θm̄`. -/
def pl6ce {L : ℕ} [NeZero L] (M : MasterFacts L) (C₁k C₁w C₁w' Clo Clb cu mbar : ℝ) : ℝ :=
  2 * pl6CEM M C₁k C₁w C₁w' Clo Clb * pl6k0 M cu + pl6Θ M C₁k C₁w C₁w' Clo Clb * mbar

theorem pl6CEM_nonneg {L : ℕ} [NeZero L] (M : MasterFacts L) {C₁k C₁w C₁w' Clo Clb : ℝ}
    (hC₁k : 0 ≤ C₁k) (hC₁w : 0 ≤ C₁w) (hC₁w' : 0 ≤ C₁w') (hClo : 0 ≤ Clo) (hClb : 0 ≤ Clb)
    (hθa0 : 0 ≤ kθ0 L M.core.A M.core.C₀a M.core.ηa) (hcx : 0 ≤ cx M.core.κ M.core.cT)
    (hct : 0 ≤ M.core.ce) : 0 ≤ pl6CEM M C₁k C₁w C₁w' Clo Clb := by
  have hK4 : 0 ≤ KM4 2 Ccut2 := KM4_nonneg 2
  have hKG : 0 ≤ Obs2.KG 2 Ccut2 4 := Obs2.KG_nonneg 2 (by norm_num)
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (d := 2) one_le_two
  have hcN : 0 ≤ Step2.cNear 2 L := by unfold Step2.cNear; exact Nat.cast_nonneg _
  have hBk : 0 ≤ kB (kθ0 L M.core.A M.core.C₀a M.core.ηa) C₁k (8 * cx M.core.κ M.core.cT) := by
    unfold kB; positivity
  have hcW := cWblk_nonneg' (L := L) hClb
  have hB' : 0 ≤ max M.core.B' 0 := le_max_right _ _
  have := cQab_nonneg
  unfold pl6CEM pl6CE pl6cG pl6cM pl6cS pl6cQ pl6aQ pl6cO pl6As pl6ρ
  positivity

set_option maxHeartbeats 8000000 in
/-- **The first summability condition for the explicit sequences** (see the module docstring). -/
theorem pl6_sum_le {L : ℕ} [NeZero L] (M : MasterFacts L) {C₁k C₁w C₁w' Clo Clb : ℝ}
    (hC₁k : 0 ≤ C₁k) (hC₁w : 0 ≤ C₁w) (hC₁w' : 0 ≤ C₁w') (hClo : 0 ≤ Clo) (hClb : 0 ≤ Clb)
    (hθ : C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) * (M.core.c * M.core.ε) ≤ 1 / 72)
    (hpow : (1 + cWblk 2 L Clb * (M.core.c * M.core.ε)) ^ (L ^ 2) ≤ 2)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N)
    (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀)
    (lam : ℕ → ℂ) {cu mbar : ℝ} (hcu : 0 ≤ cu) (hmbar : 0 ≤ mbar)
    (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) (w : List (Dir 2)) (hwl : (w.length : ℝ) ≤ 2 * sXp x) :
    ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
        (2 * (Q1 2 * (cQab * e6KQ R M C₁k C₁w mbar cu m b μ₀ lam x k) *
          (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
          eszSw R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x k +
          spE3 (Obs.coal L (0 : Lam 2 L N) x) (e6MQ R M C₁k C₁w mbar cu m b μ₀ lam x)
            (e6MS R M C₁w mbar m b μ₀ lam x) (fun _ => 3) (e6Nu R M Nh m b μ₀)
            (fun k => (w.length * (PtCorr2.histS (R.withMsq m) k
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2) k +
          2 * e6Del R M C₁k C₁w mbar cu m b μ₀ lam x w.length k * e6E R M m b μ₀ k *
            (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
          smE3 R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x)
            (pdSz R m b μ₀ w (e6M4X R M C₁k C₁w mbar cu m b μ₀ lam x))
            (e6F R M C₁k C₁w mbar cu m b μ₀ lam x w.length)
            (eszWp R M.core.c C₁w' mbar Clo Clb m b μ₀ lam x) (tauSz R m b μ₀ M.core.ce) k) ≤
      pl6ce M C₁k C₁w C₁w' Clo Clb cu mbar * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t : Flow2.Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hg : ∀ i ≤ Nh, 0 < (t i).1 ∧ (t i).1 ≤ M.core.ε := fun i hi =>
    ⟨(hadm.1 i hi).1, (hadm.1 i hi).2.1⟩
  have hε0 : 0 ≤ M.core.ε := ((hg 0 (Nat.zero_le _)).1.trans_le (hg 0 (Nat.zero_le _)).2).le
  have hc0 : 0 ≤ M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHist
    obtain ⟨hcR, -⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
    rw [← hcR]; unfold cR cV cW cZ
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have := H.hcmu; have := H.hC₂; positivity
  obtain ⟨Hap, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have hθa0 : 0 ≤ kθ0 L M.core.A M.core.C₀a M.core.ηa := by
    unfold kθ0
    have := M.core.hA2
    exact mul_nonneg M.core.hC₀a (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  obtain ⟨hct, -, -⟩ := M.tad N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hCE := pl6CEM_nonneg M hC₁k hC₁w hC₁w' hClo hClb hθa0 Hap.hcx hct
  set CE := pl6CEM M C₁k C₁w C₁w' Clo Clb with hCEd
  set CN := pl6CNM L C₁w with hCNd
  set V := vwB R m b μ₀ lam x with hVd
  have hV : 0 ≤ V := mul_nonneg (norm_nonneg _) (hg j hj).1.le
  set k₀ := pl6k0 M cu with hk₀d
  have hk₀ : 0 ≤ k₀ := by
    rw [hk₀d]; unfold pl6k0
    have := M.ιW_ge; have := M.core.hA2
    exact mul_nonneg hcu (pow_nonneg (by positivity) _)
  set r := pl6r R m b μ₀ M.core.c with hrd
  set g' : ℕ → ℝ := fun i => max (min (t i).1 M.core.ε) 0 with hg'd
  have hrg : ∀ i ≤ Nh, r i = M.core.c * g' i := fun i hi => by
    show M.core.c * max (t i).1 0 = M.core.c * max (min (t i).1 M.core.ε) 0
    rw [min_eq_left (hg i hi).2]
  have hr0 : ∀ i, 0 ≤ r i := fun i => mul_nonneg hc0 (le_max_right _ _)
  -- per scale
  have hitem := fun k (hk : k ∈ Finset.Ico j (Nh + 1)) =>
    pl6_item_le M hC₁k hC₁w hC₁w' hClo hClb hθ hpow N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀
      hadm lam hcu hmbar x hx h1 hj w hwl k (mem_Ico.1 hk).1 (by have := (mem_Ico.1 hk).2; omega)
  refine (sum_le_sum hitem).trans ?_
  simp only [← hVd, ← hjd, ← hk₀d, ← hrd, ← hCEd, ← hCNd, ← ht]
  rw [sum_add_distrib]
  -- the `k = N_h` term
  have hNt : ∑ k ∈ Finset.Ico j (Nh + 1), (if k < Nh then (0 : ℝ) else
      V * (CN * (mbar * (M.core.c * M.core.ε)))) = V * (CN * (mbar * (M.core.c * M.core.ε))) := by
    rw [sum_Ico_succ_top hj, if_neg (lt_irrefl _)]
    rw [sum_eq_zero fun k hk => if_pos (mem_Ico.1 hk).2, zero_add]
  rw [hNt]
  -- the normal forms, summed with `pairLoop2_sum_le`
  have hG2 : ∑ k ∈ Finset.Ico j (Nh + 1), g' k ^ 2 ≤ pl6G2 L M.core.ε := by
    have hβL : 0 < betaL L := lt_of_lt_of_le (by norm_num) (betaL_ge (by have := M.core.hL49; omega))
    have hinc := M.ginc N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
    have hS := sum_gsq_Ico_le (g := fun i => (t i).1) hβL hj (fun k hk hkn => hinc k hkn)
    have e : ∑ k ∈ Finset.Ico j Nh, g' k ^ 2 = ∑ k ∈ Finset.Ico j Nh, ((t k).1) ^ 2 :=
      sum_congr rfl fun k hk => by
        rw [hg'd]; dsimp only
        rw [min_eq_left (hg k (by have := (mem_Ico.1 hk).2; omega)).2,
          max_eq_left (hg k (by have := (mem_Ico.1 hk).2; omega)).1.le]
    rw [sum_Ico_succ_top hj, e]
    have h2 : g' Nh ^ 2 ≤ M.core.ε ^ 2 := by
      rw [hg'd]; dsimp only
      exact pow_le_pow_left₀ (le_max_right _ _) (max_le (min_le_right _ _) hε0) 2
    have h3 : 4 / betaL L * ((t Nh).1 - (t j).1) ≤ 4 * M.core.ε / betaL L := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hβL.le
      have := (hg Nh le_rfl).2; have := (hg j hj).1; nlinarith
    unfold pl6G2; linarith
  have hs : ∀ k ∈ Finset.Ico j (Nh + 1), V * (CE * pl6NF j k₀ mbar r k) ≤
      V * CE * pl6P j k₀ k + CE * (V * mbar) * ((M.core.c * g' k) ^ 2 +
        ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) * ((M.core.c * g' i) ^ 2 +
          (M.core.c * g' i) * (M.core.c * g' k)) + (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k)) := by
    intro k hk
    have hkN : k ≤ Nh := by have := (mem_Ico.1 hk).2; omega
    have hQ : pl6Q j r k ≤ ∑ i ∈ Finset.Ico j k, (1 / 2 : ℝ) ^ (k - i) * ((M.core.c * g' i) ^ 2 +
        (M.core.c * g' i) * (M.core.c * g' k)) := by
      unfold pl6Q
      refine sum_le_sum fun i hi => ?_
      have hiN : i ≤ Nh := by have := (mem_Ico.1 hi).2; omega
      rw [hrg i hiN]
      have : 0 ≤ (M.core.c * g' i) * (M.core.c * g' k) := by
        rw [← hrg i hiN, ← hrg k hkN]; exact mul_nonneg (hr0 i) (hr0 k)
      have : 0 ≤ (1 / 2 : ℝ) ^ (k - i) := by positivity
      nlinarith
    have hlast : 0 ≤ (1 / 2 : ℝ) ^ (k - j) * (M.core.c * g' k) := by
      rw [← hrg k hkN]; exact mul_nonneg (by positivity) (hr0 k)
    have hCm : 0 ≤ CE * (V * mbar) := by positivity
    unfold pl6NF pl6G0
    rw [hrg k hkN]
    have e : V * (CE * (pl6P j k₀ k + mbar * pl6Q j r k + mbar * (M.core.c * g' k) ^ 2)) =
        V * CE * pl6P j k₀ k + CE * (V * mbar) * ((M.core.c * g' k) ^ 2 + pl6Q j r k) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left (add_le_add_left hQ ((M.core.c * g' k) ^ 2)) hCm
    nlinarith
  have hsum := pairLoop2_sum_le (q := 1 / 2) (by norm_num) le_rfl hc0 hCE (mul_nonneg hV hmbar)
    (g := g') (fun i => le_max_right _ _) (fun i => max_le (min_le_right _ _) hε0)
    (s := fun k => V * (CE * pl6NF j k₀ mbar r k)) (seed := fun k => V * CE * pl6P j k₀ k) hG2 hs
  have hseed : ∑ k ∈ Finset.Ico j (Nh + 1), V * CE * pl6P j k₀ k ≤ 2 * (V * CE * k₀) := by
    have h := geom_decay_le (q := 1 / 2) (by norm_num) le_rfl (g := fun _ => (1 : ℝ))
      (fun _ => zero_le_one) (fun _ => le_rfl) j (Nh + 1)
    unfold pl6P
    have e : ∑ k ∈ Finset.Ico j (Nh + 1), V * CE * ((1 / 2 : ℝ) ^ (k - j) * k₀) =
        V * CE * k₀ * ∑ k ∈ Finset.Ico j (Nh + 1), (1 / 2 : ℝ) ^ (k - j) * 1 := by
      rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    rw [e]
    have : 0 ≤ V * CE * k₀ := by positivity
    nlinarith
  have hfin : V * (pl6ce M C₁k C₁w C₁w' Clo Clb cu mbar) = 2 * (V * CE * k₀) +
      CE * (V * mbar) * (6 * M.core.c ^ 2 * pl6G2 L M.core.ε + 2 * M.core.c * M.core.ε) +
      V * (CN * (mbar * (M.core.c * M.core.ε))) := by
    unfold pl6ce pl6Θ; rw [← hCEd, ← hCNd, ← hk₀d]; ring
  have e2 : pl6ce M C₁k C₁w C₁w' Clo Clb cu mbar * ‖Mmag R m b μ₀ lam j‖ * (t j).1 =
      V * pl6ce M C₁k C₁w C₁w' Clo Clb cu mbar := by
    rw [hVd]; show _ = (‖Mmag R m b μ₀ lam j‖ * (t j).1) * _; ring
  refine le_trans ?_ (le_of_eq e2.symm)
  rw [hfin]
  linarith

set_option maxHeartbeats 8000000 in
/-- **`PairJointSizesP3` with the first summability condition discharged** (task 2;
`pairJointSizesP3_of_VS` + `pl6_sum_le`). The constants are those of `pairJointSizesP3_of_VS`;
the `ε`-requirements are the hypotheses `hθ` (decay of the small-set recursion) and `hpow` (the
product part of `𝒲'`); `c_e = pl6ce … c_u m̄`. -/
theorem pairJointSizesP3_closed : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ M : MasterFacts L,
    ∃ C₁v C₁k C₁w C₁w' Clo Clb : ℝ, 0 ≤ C₁v ∧ 0 ≤ C₁k ∧ 0 ≤ C₁w ∧ 0 ≤ C₁w' ∧ 0 ≤ Clo ∧ 0 ≤ Clb ∧
    (C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 1) * (M.core.c * M.core.ε) ≤ 1 / 72 →
      (1 + cWblk 2 L Clb * (M.core.c * M.core.ε)) ^ (L ^ 2) ≤ 2 →
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
    ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (cu ca cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 ≤ cu → 0 < mbar →
      cr ≤ mbar → 0 ≤ ca →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
        vck C₁v * ((4 * C₁v + 1) * mbar) →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
      8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w' + 1) * mbar →
      PairJointSizesP3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd)
        (pl6ce M C₁k C₁w C₁w' Clo Clb cu mbar) ca cr) := by
  obtain ⟨L₀, hL₀⟩ := pairJointSizesP3_of_VS
  refine ⟨L₀, fun L _ hL M => ?_⟩
  obtain ⟨C₁v, C₁k, C₁w, C₁w', Clo, Clb, hC₁v, hC₁k, hC₁w, hC₁w', hClo, hClb, H⟩ := hL₀ L hL M
  refine ⟨C₁v, C₁k, C₁w, C₁w', Clo, Clb, hC₁v, hC₁k, hC₁w, hC₁w', hClo, hClb, ?_⟩
  intro hθ hpow N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu ca cr mbar hU hcu hmbar
    hcr hca h8v h8 h8'
  exact H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu _ ca cr mbar hU hmbar hcr hca
    h8v h8 h8' fun x hx h1 hj w _ hwl =>
      pl6_sum_le M hC₁k hC₁w hC₁w' hClo hClb hθ hpow N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀
        hadm lam hcu hmbar.le x hx h1 hj w hwl


/-- **The conclusion of `pairJointSizesP3_closed` at given constants** (after the two
requirements). -/
def PJClosedP {L : ℕ} [NeZero L] (M : MasterFacts L) (C₁v C₁k C₁w C₁w' Clo Clb : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀,
    Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
  ∀ (lam : ℕ → ℂ) (cu ca cr mbar : ℝ), PairUnitSeed R Nh m b μ₀ lam cu → 0 ≤ cu → 0 < mbar →
    cr ≤ mbar → 0 ≤ ca →
    8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤
      vck C₁v * ((4 * C₁v + 1) * mbar) →
    8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w + 1) * mbar →
    8 * (cu * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ (4 * C₁w' + 1) * mbar →
    PairJointSizesP3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd)
      (pl6ce M C₁k C₁w C₁w' Clo Clb cu mbar) ca cr

set_option maxHeartbeats 8000000 in
/-- **`PairJointSizesP3` with the first summability condition discharged, at the exported
constants and without requirements**: `C₁k = C₁ka`, `C₁w = C₁w' = C₁wa` (`MasterCore.abwHistC`),
`C_lo = cwClo`, `C_lb = cwClb` (`MasterCore.hWpo`); the requirements `hθ`, `hpow` are the
`MasterCore` fields `hEaB`, `hpowF` (from `pairEReq`). -/
theorem pairJointSizesP3_closedC {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ C₁v : ℝ, 0 ≤ C₁v ∧ PJClosedP M C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb := by
  obtain ⟨hClo, hClb, -⟩ := cw_wpo_spec
  obtain ⟨-, hC₁k, -, hθ, -, -, -, hC₁w, -⟩ := M.core.hEaB
  have hAH := M.core.abwHistC
  obtain ⟨C₁v, hC₁v, H⟩ :=
    pairJointSizesP3_of_VSat M M.core.hWpo hClo hClb hC₁k hC₁w hC₁w hAH hAH
  refine ⟨C₁v, hC₁v, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu ca cr mbar hU hcu hmbar
    hcr hca h8v h8 h8'
  exact H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam cu _ ca cr mbar hU hmbar hcr hca
    h8v h8 h8' fun x hx h1 hj w _ hwl =>
      pl6_sum_le M hC₁k hC₁w hC₁w hClo hClb hθ M.core.hpowF N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
        b μ₀ hadm lam hcu hmbar.le x hx h1 hj w hwl

end

end Spin2
