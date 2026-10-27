import Spin2.Cont.ContEqC5
import Spin2.Cont.ContEq3
import Spin2.Cont.ContShift

set_option autoImplicit false

/-!
# B3, `r`-dependent form, item (d): all nearby pairs away from the origin

* **`eqc_region`** (pure): `L^J + 2D ≤ 2|x|_∞` and `|z − x|_∞ ≤ D` give `J ≤ j(0, z)`;
* **`eqc_fallback`** (pure, small `m_s`): a pointwise bound `|F| ≤ B` on the `D`-ball gives
  `|F x − F y| ≤ 2B`;
* **`MasterFacts.eqc_all_pairs (hcab)`**: under the shared scalar hypotheses (those of
  `fin_T6_mid` and `fin_conn_diff_top` that do not depend on the pair) and the per-pair packages
  `EqcMidPkg`/`EqcTopPkg` for all good pairs `(p, q)` with `J ≤ j(0, p)`, `J ≤ j(0, q)`
  (intermediate case, `j(0, q) ≤ N_h`) resp. `N_h + 1 ≤ j(0, q)` (top case):
  for every `x` whose `L^{ms−r}`-ball lies in `{J ≤ j(0, ·)}` and every `y` with
  `|y − x|_∞ ≤ L^{ms−r}`,
  `|P(x) − P(y)| ≤ 2·max(eqcCmid(K_A, K_R, C_δ), eqcCtop(K_A', K_E'))·cddRel·ϑ_{N_h}²`
  (`ms < J`, `N ≤ J + C_δ`, `1 ≤ r ≤ ms < N_h`). The boundary `j_y = N_h` vs `N_h + 1` is the case
  split of the proof; the intermediate point of `eq_pair_chain` lies in the region, hence
  `ms < j_x` for it.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

/-- **The region**: `L^J + 2D ≤ 2|x|_∞` keeps the `D`-ball of `x` in `{J ≤ j(0, ·)}`. -/
theorem eqc_region {N : ℕ} (hL : 2 ≤ L) {J D : ℕ} (x : Lam 2 L N)
    (h : L ^ J + 2 * D ≤ 2 * supNorm x) :
    ∀ z : Lam 2 L N, supNorm (z - x) ≤ D → J ≤ Obs.coal L (0 : Lam 2 L N) z := by
  intro z hz
  rw [cs_coal_zero]
  have h1 := supNorm_add_le z (x - z)
  rw [add_sub_cancel] at h1
  have h2 : supNorm (x - z) = supNorm (z - x) := by rw [← neg_sub, supNorm_neg]
  refine Nat.le_log_of_pow_le (by omega) ?_
  omega

/-- **Fallback** (small `m_s`): a pointwise bound on the `D`-ball of `x`. -/
theorem eqc_fallback {N : ℕ} (F : Lam 2 L N → ℝ) {D : ℕ} {B : ℝ} (x y : Lam 2 L N)
    (hB : ∀ z : Lam 2 L N, supNorm (z - x) ≤ D → |F z| ≤ B) (hxy : supNorm (y - x) ≤ D) :
    |F x - F y| ≤ 2 * B := by
  have hx := hB x (by rw [sub_self, supNorm_zero]; exact Nat.zero_le _)
  have hy := hB y hxy
  calc |F x - F y| ≤ |F x| + |F y| := abs_sub _ _
    _ ≤ 2 * B := by linarith

namespace MasterFacts

variable (M : MasterFacts L)

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **All nearby pairs away from the origin** (item (d)). -/
theorem eqc_all_pairs (hcab : 0 < M.k2cab) : ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧
    0 ≤ C₁v ∧ 0 ≤ C₁m ∧
    ∀ {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (M.core.A / 2) r₀)
    {Kt : ℝ}
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2)
    (hmA : 8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hsmA : (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) +
        9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
        cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 / 2)
    (hs1 : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ M.core.ρ)
    (hs2 : 8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
      ≤ 1 / 2)
    (hs3 : PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1)
    (hs4 : 4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ r₀ ^ 2)
    (hs5 : cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ r₀)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 / 2)
    (hspl : SplitSmall R.P L R.ρ) (hm0' : 0 < m) (hmL : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    {cK0 : ℝ} (hseed : TopSeedAt R Nh m b (b - m) cK0)
    (hvb : cM * M.core.ℓ ^ 2 * (4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) +
      8 * M.core.ℓ ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1)
    (hwb : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2) ≤ 1)
    {ms r : ℕ} (hk0 : 0 < ms) (hkN : ms < Nh) (hrk : r ≤ ms) (hr1 : 1 ≤ r)
    (hs0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms))
    (hs : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) ≤ 1 / 2)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 3) ≤ 1)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) *
      2) ≤ 1 / 1344)
    {J Cδ : ℕ} (hmsJ : ms < J) (hJδ : N ≤ J + Cδ) {KA KR KA' KE' : ℝ}
    (hmidP : ∀ p q : Lam 2 L N, EqGood ms (L ^ (ms - r)) p q → J ≤ Obs.coal L (0 : Lam 2 L N) p →
      J ≤ Obs.coal L (0 : Lam 2 L N) q → Obs.coal L (0 : Lam 2 L N) q ≤ Nh →
      M.EqcMidPkg C₁w C₁t C₁v C₁m Λ₁ Λ₂ R m b Nh r₀ p q ms r Cδ KA KR)
    (htopP : ∀ p q : Lam 2 L N, EqGood ms (L ^ (ms - r)) p q → J ≤ Obs.coal L (0 : Lam 2 L N) p →
      Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) q → M.EqcTopPkg R m b Nh r₀ p q ms r KA' KE')
    (x y : Lam 2 L N)
    (hxJ : ∀ z : Lam 2 L N, supNorm (z - x) ≤ L ^ (ms - r) → J ≤ Obs.coal L (0 : Lam 2 L N) z)
    (hxy : supNorm (y - x) ≤ L ^ (ms - r)),
    |Pconn L N (1 / b) x - Pconn L N (1 / b) y| ≤
      2 * (max (M.eqcCmid KA KR Cδ) (M.eqcCtop KA' KE') *
        M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
          (R.withMsq m).A r * varthJ R m b (b - m) Nh ^ 2) := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, hT⟩ := M.eqc_mid_pkg hcab
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall hspl hm0' hmL cK0 hseed hvb hwb ms r hk0 hkN hrk hr1 hs0 hs hreg hg J Cδ
    hmsJ hJδ KA KR KA' KE' hmidP htopP x y hxJ hxy
  have hN2 : 2 ≤ N := by omega
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hc0 : 0 ≤ M.core.c := by linarith [M.eqc_c_ge R hP hi0 hRℓ hRA hRρ hN2 hNh hm]
  have hε : 0 ≤ M.core.ε := (hD 0 (Nat.zero_le _)).1.le.trans (hD 0 (Nat.zero_le _)).2.1
  have hA0 : 0 ≤ (R.withMsq m).A := (Fact.out : 0 < R.A).le
  have hι : 0 ≤ rpIota 0 0 := by unfold rpIota; positivity
  have hQ0 := M.eqc_cddRel_nonneg r hc0 hε (hD ms (by omega)).1.le (zA_nonneg L hm.1.le ms) hι hA0
  have hV0 : 0 ≤ varthJ R m b (b - m) Nh := Real.rpow_nonneg (div_pos hb (hD Nh le_rfl).1).le _
  have hX : 0 ≤ M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
      (rpIota 0 0) (R.withMsq m).A r * varthJ R m b (b - m) Nh ^ 2 := by positivity
  have hL2 : 2 ≤ L := by have := M.core.hL49; omega
  have hDl : L ^ (ms - r) < L ^ ms := Nat.pow_lt_pow_right (by omega) (by omega)
  have hne : ∀ q : Lam 2 L N, J ≤ Obs.coal L (0 : Lam 2 L N) q → q ≠ 0 := by
    intro q hq h
    subst h
    rw [cs_coal_zero, supNorm_zero, mul_zero, Nat.log_zero_right] at hq
    omega
  refine eq_abs_sub_le_two hDl (fun z => J ≤ Obs.coal L (0 : Lam 2 L N) z) (Pconn L N (1 / b))
    (max (M.eqcCmid KA KR Cδ) (M.eqcCtop KA' KE') *
      M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
        (R.withMsq m).A r * varthJ R m b (b - m) Nh ^ 2) ?_ x y hxJ hxy
  intro p q hp hq hpq
  obtain ⟨hblk, hdist⟩ := hpq
  rcases Nat.lt_or_ge Nh (Obs.coal L (0 : Lam 2 L N) q) with htop | hmid
  · have h := M.eqc_top_pkg R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hseed hK hmT hmA hsmA
      hs1 hs2 hs3 hs4 hs5 hvb hwb hsmall q (hne q hq) htop hspl p hk0 hkN (by omega) hrk hblk hdist
      hs0 hs hreg hg hcab (htopP p q ⟨hblk, hdist⟩ hp htop)
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hQ0)
      (by positivity))
  · have h := hT R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1 hs2 hs3 hs4 hs5
      hsmall hspl hm0' hmL p q (hne q hq) (by omega) hmid hk0 (by omega) (by omega) hrk hblk hdist
      hs0 hs hreg hg Cδ (by omega) (hmidP p q ⟨hblk, hdist⟩ hp hq hmid)
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hQ0)
      (by positivity))

end MasterFacts

end

end Spin2
