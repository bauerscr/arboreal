import Spin2.Pair.PairAbove
import Spin2.Pair.ZeroNormA
import Spin2.Gam.GamLastBd
import Spin2.Gam.GamTop
import PtCorr2.Zero.OnePtWin

/-!
# Route (a1), input (i): the exact one-point identity on windowed trajectories

Along the pair history at a point `x` (`zV b`, `ptsX x`), at **any sign of `h`**, given only
`⟨Z_0⟩ ≠ 0` (no positivity):

* **`onePt_split_win`**: `r = 1 − b⟨ψ̄_0ψ_0⟩ = γ_{a,N} + n_aΩ` (the one-point closure of
  `pair_E_split` without `b ≤ μ₀ + m²`), with `γ_{a,N} = gamNa` the `σ_a` constant of the observable
  chain up to scale `N` and `n_aΩ = sA Ω/sE Ω` the zero-mode part (`Ω = zZm`), together with the
  factorisation `⟨Z_0⟩ = (∏_j c_j)·(det_{N−1}·e^{−u^{obs,∅}_N}·sE Ω)`;
* **`sE_zZm_eq`**: comparing with the bulk chain `⟨Z_0⟩ = (∏_j c_j)·det_{N−1}·e^{−u_N}·U`
  (`hist_omega_traj`, `U = 1 + ũ`): `sE Ω = U·e^{u^{obs,∅}_N − u_N}`. The observable last step
  moves `∑_B Loc_{Λ,B}S(Λ)` from `𝒲_N` into `u_N`; this is the only difference
  (`zUB_sub_u_eq`: `u^{obs,∅}_N − u_N = −∑_B ε(Loc_{Λ,B}S(Λ))`), bounded by `L⁴C_fǧ²`
  (`zUB_sub_u_le`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

/-- **The zero-mode part of the one-point function, bounded** (pure): with
`sA = εF_a − c·c2F_a`, `c = t_raw/V`, `|c2F_a − β| ≤ ½|β|`, `|εF_a| ≤ K_A|β|/z`,
`|m²zt_raw − 1| ≤ K_Tm²V`, `s = U e^δ`, `|δ| ≤ E_u`, `n = m²V·U`, `Re n ≥ n_lo > 0`:
`|sA/s| ≤ e^{E_u}(|β|/z)(K_Am²V + (3/2)(1 + K_Tm²V))/n_lo`. -/
theorem nA_zm_le {sA s U δ n β c cF eF tr : ℂ} {z m V KA KT Eu nlo : ℝ}
    (hz : 0 < z) (hm : 0 < m) (hV : 0 < V)
    (hsA : sA = eF - c * cF) (hc : c = tr / (V : ℂ))
    (hcF : ‖cF - β‖ ≤ 1 / 2 * ‖β‖) (heF : ‖eF‖ ≤ KA * ‖β‖ / z)
    (htr : ‖(m : ℂ) * ((z : ℂ) * tr) - 1‖ ≤ KT * (m * V))
    (hs : s = U * Complex.exp δ) (hδ : ‖δ‖ ≤ Eu)
    (hn : ((m * V : ℝ) : ℂ) * U = n) (hnlo : 0 < nlo) (hnre : nlo ≤ n.re) :
    ‖sA / s‖ ≤ Real.exp Eu * (‖β‖ / z) * (KA * (m * V) + 3 / 2 * (1 + KT * (m * V))) / nlo := by
  set X := m * V with hX
  have hX0 : 0 < X := mul_pos hm hV
  have htr1 : m * z * ‖tr‖ ≤ 1 + KT * X := by
    have h := norm_le_insert' ((m : ℂ) * ((z : ℂ) * tr)) 1
    rw [norm_one] at h
    have e : ‖(m : ℂ) * ((z : ℂ) * tr)‖ = m * z * ‖tr‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hm.le,
        Real.norm_of_nonneg hz.le, mul_assoc]
    linarith
  have hcF' : ‖cF‖ ≤ 3 / 2 * ‖β‖ := by
    have := norm_le_insert' cF β; linarith
  have hcn : ‖c‖ = ‖tr‖ / V := by
    rw [hc, norm_div, Complex.norm_real, Real.norm_of_nonneg hV.le]
  have hβ0 := norm_nonneg β
  have hsAb : ‖sA‖ * X ≤ ‖β‖ / z * (KA * X + 3 / 2 * (1 + KT * X)) := by
    rw [hsA]
    have h1 : ‖eF - c * cF‖ ≤ ‖eF‖ + ‖c‖ * ‖cF‖ := by
      rw [← norm_mul]; exact norm_sub_le _ _
    have h2 : ‖c‖ * ‖cF‖ * X ≤ ‖β‖ / z * (3 / 2 * (1 + KT * X)) := by
      rw [hcn]
      have e : ‖tr‖ / V * ‖cF‖ * X = (m * z * ‖tr‖) * ‖cF‖ / z := by
        rw [hX]; field_simp
      rw [e]
      have := mul_le_mul htr1 hcF' (norm_nonneg _)
        (((by positivity : (0 : ℝ) ≤ m * z * ‖tr‖)).trans htr1)
      calc m * z * ‖tr‖ * ‖cF‖ / z ≤ (1 + KT * X) * (3 / 2 * ‖β‖) / z :=
            div_le_div_of_nonneg_right this hz.le
        _ = ‖β‖ / z * (3 / 2 * (1 + KT * X)) := by ring
    have h3 : ‖eF‖ * X ≤ ‖β‖ / z * (KA * X) := by
      have := mul_le_mul_of_nonneg_right heF hX0.le
      calc ‖eF‖ * X ≤ KA * ‖β‖ / z * X := this
        _ = ‖β‖ / z * (KA * X) := by ring
    calc ‖eF - c * cF‖ * X ≤ (‖eF‖ + ‖c‖ * ‖cF‖) * X := mul_le_mul_of_nonneg_right h1 hX0.le
      _ = ‖eF‖ * X + ‖c‖ * ‖cF‖ * X := by ring
      _ ≤ _ := by linarith
  have hU : nlo ≤ X * ‖U‖ := by
    have h1 : ‖n‖ = X * ‖U‖ := by
      rw [← hn, norm_mul, Complex.norm_real, Real.norm_of_nonneg hX0.le]
    have h2 := Complex.re_le_norm n
    linarith
  have hE : Real.exp (-Eu) ≤ ‖Complex.exp δ‖ := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have h1 := Complex.abs_re_le_norm δ
    have h2 := neg_abs_le δ.re
    linarith
  have hs0 : nlo * Real.exp (-Eu) ≤ X * ‖s‖ := by
    rw [hs, norm_mul]
    have := mul_le_mul hU hE (Real.exp_pos _).le (by positivity)
    linarith [show X * (‖U‖ * ‖Complex.exp δ‖) = X * ‖U‖ * ‖Complex.exp δ‖ by ring]
  have hsp : 0 < ‖s‖ := by
    rcases (norm_nonneg s).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hs0
      linarith [mul_pos hnlo (Real.exp_pos (-Eu))]
  rw [norm_div, div_le_iff₀ hsp]
  set Q := ‖β‖ / z * (KA * X + 3 / 2 * (1 + KT * X)) with hQ
  have key : ‖sA‖ * (nlo * Real.exp (-Eu)) ≤ Q * ‖s‖ := by
    calc ‖sA‖ * (nlo * Real.exp (-Eu)) ≤ ‖sA‖ * (X * ‖s‖) :=
          mul_le_mul_of_nonneg_left hs0 (norm_nonneg _)
      _ = ‖sA‖ * X * ‖s‖ := by ring
      _ ≤ Q * ‖s‖ := mul_le_mul_of_nonneg_right hsAb (norm_nonneg _)
  have hEe : Real.exp (-Eu) * Real.exp Eu = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have e : Real.exp Eu * (‖β‖ / z) * (KA * X + 3 / 2 * (1 + KT * X)) / nlo * ‖s‖ =
      Q * ‖s‖ * Real.exp Eu / nlo := by rw [hQ]; ring
  rw [e, le_div_iff₀ hnlo]
  have := mul_le_mul_of_nonneg_right key (Real.exp_pos Eu).le
  calc ‖sA‖ * nlo = ‖sA‖ * nlo * (Real.exp (-Eu) * Real.exp Eu) := by rw [hEe, mul_one]
    _ = ‖sA‖ * (nlo * Real.exp (-Eu)) * Real.exp Eu := by ring
    _ ≤ Q * ‖s‖ * Real.exp Eu := this

/-- **`Re r ≥ 0` from the split** (pure): `r = γ + w`, `|γ − ϑ| ≤ e₁ϑ`, `|w| ≤ e₂ϑ`, `e₁ + e₂ ≤ 1`. -/
theorem re_nonneg_of_split {r γ w : ℂ} {v e1 e2 : ℝ} (hv : 0 ≤ v) (hr : r = γ + w)
    (hγ : ‖γ - (v : ℂ)‖ ≤ e1 * v) (hw : ‖w‖ ≤ e2 * v) (he : e1 + e2 ≤ 1) : 0 ≤ r.re := by
  have h1 := (abs_le.1 ((Complex.abs_re_le_norm (γ - (v : ℂ))).trans hγ)).1
  have h2 := (abs_le.1 ((Complex.abs_re_le_norm w).trans hw)).1
  rw [Complex.sub_re, Complex.ofReal_re] at h1
  rw [hr, Complex.add_re]
  have h3 : e1 * v + e2 * v ≤ v := by nlinarith
  linarith

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The bulk constant `u^{obs,∅}_N(Λ)` of the observable last step (pair history at `x`). -/
def zUB (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : ℂ :=
  Obs2.uXB (ptsX x) (Nh + 1)
    (LastN.stCovN (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st)
    (Obs2.fullV (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re
      (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (Obs2.fullW (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D
      (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (Obs2.fullK (R.withMsq m) (Nh + 1)
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
      (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K
      (Obs2.obsHist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    univ

set_option maxHeartbeats 2000000 in
/-- **The one-point closure at any sign of `h`** (given `⟨Z_0⟩ ≠ 0`):
`1 − b⟨ψ̄_0ψ_0⟩ = γ_{a,N} + n_aΩ`, `sE Ω ≠ 0`, and the bulk factorisation of `⟨Z_0⟩` through the
observable chain. -/
theorem onePt_split_win {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt (R.withMsq m) j)
    (hVL : ValidAtL (R.withMsq m) Nh) (hL7 : 7 ≤ L) {b μ₀ : ℝ} (hb : 0 < b) (x : Lam 2 L N)
    (hZ : omegaC (Γh (R.withMsq m) 0 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (Zh (R.withMsq m) 0 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : Alg 2 L N) ≠ 0) :
    PtCorr2.sE (zZm R Nh m b μ₀ x) ≠ 0 ∧
      1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0) =
        gamNa R Nh m b μ₀ x + PtCorr2.nA (zZm R Nh m b μ₀ x) ∧
      omegaC (Γh (R.withMsq m) 0 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (Zh (R.withMsq m) 0 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : Alg 2 L N) =
      (∏ j ∈ range (Nh + 1), ch (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) *
        (detStep (R.withMsq m) (Nh + 1)
            (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st *
          (Complex.exp (-zUB R Nh m b μ₀ x) * PtCorr2.sE (zZm R Nh m b μ₀ x))) := by
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set o₀ := Obs2.obsInit .two (zV b) (ptsX x) with ho₀
  set Pr := rgProdO (R.withMsq m) (ptsX x) o₀ Nh t with hPr
  obtain ⟨ke, ka⟩ := onept_rg_ratioZ (R.withMsq m) (ptsX x) hN hρ1 hspl hm0 hm hV hVL hL7 b μ₀
    (zV b)
  have hP0 : PtCorr2.sE Pr ≠ 0 := by
    have : PtCorr2.sE Pr = omegaC (Γh (R.withMsq m) 0 t) (Zh (R.withMsq m) 0 t : Alg 2 L N) := ke
    rw [this]; exact hZ
  have hfac : PtCorr2.sE Pr = _ := sE_rgProdO_eq (R.withMsq m) (ptsX x) o₀ Nh t
  -- the split at `k = N_h + 1`
  have hs := rgProdO_split (R.withMsq m) (ptsX x) o₀ (k := Nh + 1) (Nh := Nh) le_rfl t
  have hHi : prodHi (R.withMsq m) (ptsX x) o₀ Nh (Nh + 1) t =
      zCst R Nh m b μ₀ x (Nh + 1) * zZm R Nh m b μ₀ x := by
    unfold prodHi lastO zCst zUo zZm zFin zCc
    simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    rfl
  rw [hHi] at hs
  set X0 := prodLo (R.withMsq m) (ptsX x) o₀ (Nh + 1) t with hX0d
  set X1 := zCst R Nh m b μ₀ x (Nh + 1) with hX1d
  set Ω := zZm R Nh m b μ₀ x with hΩd
  have hP0' : PtCorr2.sE (X0 * (X1 * Ω)) ≠ 0 := by rw [← hs]; exact hP0
  rw [PtCorr2.sE_mul, PtCorr2.sE_mul] at hP0'
  have hX0 : PtCorr2.sE X0 ≠ 0 := fun h => hP0' (by rw [h, zero_mul])
  have hX1 : PtCorr2.sE X1 ≠ 0 := fun h => hP0' (by rw [h, zero_mul, mul_zero])
  have hΩ : PtCorr2.sE Ω ≠ 0 := fun h => hP0' (by rw [h, mul_zero, mul_zero])
  refine ⟨hΩ, ?_, ?_⟩
  · -- `⟨Z_0⟩ ≠ 0` in the model form
    have ht := traj_zero_eq (R.withMsq m) b μ₀
    have hZb : Obs.Zb (Suscept.Cov 2 L N m) (VE (V0c b μ₀) (univ : Finset (Lam 2 L N))) ≠ 0 := by
      have := omega_Zh_zero_eq (R.withMsq m) hL7 hm0 (by omega) t hb ht
      rw [Vh_eq_V0 (msq := (R.withMsq m).msq) hb] at this
      intro h0; exact hZ (this.trans h0)
    have hra : PtCorr2.avg0 L N m b μ₀ (PtCorr2.zObsA (zV b) (ptsX x)) =
        1 - (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi 0) := by
      rw [zObsA_zV]; exact Ward.avg_one_sub_smul _ _ hZb _ _
    have ha : PtCorr2.avg0 L N m b μ₀ (PtCorr2.zObsA (zV b) (ptsX x)) =
        PtCorr2.sA Pr / PtCorr2.sE Pr := ka hP0
    rw [hra] at ha
    rw [ha]
    have e1 : PtCorr2.sA Pr / PtCorr2.sE Pr = PtCorr2.nA (X0 * (X1 * Ω)) := by
      unfold PtCorr2.nA; rw [← hs]
    have hX1Ω : PtCorr2.sE (X1 * Ω) ≠ 0 := by rw [PtCorr2.sE_mul]; exact mul_ne_zero hX1 hΩ
    rw [e1, PtCorr2.nA_mul hX0 hX1Ω, PtCorr2.nA_mul hX1 hΩ]
    obtain ⟨ea, -⟩ := PtCorr2.prodLo_sA_sB (R.withMsq m) (ptsX x) o₀ rfl t (Nh + 1)
    have hA : PtCorr2.nA X0 = uA R m b μ₀ x (Nh + 1) := by
      unfold PtCorr2.nA
      rw [ea, mul_div_cancel_left₀ _ hX0]; rfl
    rw [hA, ← add_assoc, uA_add_nA_zCst R Nh m b μ₀ x le_rfl hX1]
  · rw [← ke]; exact hfac

/-- **The bulk constants of the two last steps differ by the localised `S(Λ)`**:
`u^{obs,∅}_N(Λ) − u_N(Λ) = −∑_B ε(Loc_{Λ,B}S(Λ))` (no `Q` at the last scale). -/
theorem zUB_sub_u_eq {Nh : ℕ} (hNh : Nh + 2 = N) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    zUB R Nh m b μ₀ x - (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u =
      -∑ b' ∈ blocks (Nh + 1) (univ : Finset (Lam 2 L N)),
        ε (LS (Nh + 1) (LastN.stCovN (R.withMsq m) (Nh + 1)
            (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st)
          (stVf (R.withMsq m) (Nh + 1)
            (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st
            (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).g.re
            (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).nu.re)
          ((histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).st.Wl +
            (histOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).D) b' :
          Alg 2 L N) := by
  have ho := Obs2.obsHist_isObs (R.withMsq m) (ptsX x) _
    (Obs2.obsInit_isObs .two (zV b) (ptsX x)) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
  unfold zUB
  rw [Obs2.uXB_eq, Obs2.bulkF_fullV (ho := ho), Obs2.bulkF_fullW (ho := ho),
    Obs2.bulkF_fullK (ho := ho)]
  show Step2.uX _ _ _ _ _ _ - LastN.uXN _ _ _ _ = _
  unfold Step2.uX LastN.uXN
  rw [← sum_sub_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun b' _ => ?_
  unfold Step2.up LastN.upN Step2.uVp
  have hQ : ∀ K : Act 2 L N, Q2 (Nh + 1) K b' = 0 := fun K => by
    unfold Q2; rw [if_neg (by omega)]
  rw [hQ, EthE_zero]
  simp only [sub_zero, AddSubgroupClass.coe_sub, map_sub]
  ring

/-- **`|u^{obs,∅}_N − u_N| ≤ L⁴C_fǧ²`** (`GlueOut`: `|εS(B)| ≤ C_fǧ²`, `L²` blocks, `eps_LS_le`). -/
theorem zUB_sub_u_le {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Cf : ℝ} (hCf : 0 ≤ Cf) (x : Lam 2 L N)
    (hG : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (hρ0 : 0 ≤ R.ρ)
    (hρ1 : R.ρ < 1) :
    ‖zUB R Nh m b μ₀ x - (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).u‖ ≤
      (L : ℝ) ^ 4 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ^ 2) := by
  have hℓ : 0 < (R.withMsq m).ℓ := Fact.out
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set st := (histOut (R.withMsq m) Nh t).st with hst
  set C := LastN.stCovN (R.withMsq m) (Nh + 1) st
  set w := Cf * (t Nh).1 ^ 2 with hw
  have hw0 : 0 ≤ w := by positivity
  obtain ⟨-, -, -, -, -, hB, -⟩ := hG.2
  have hZ : (lastOut (R.withMsq m) Nh t).Z ≠ 0 := lastOut_Z_ne (R.withMsq m) hρ0 hρ1 Nh t
  have hh : 0 < fscale (lastOut (R.withMsq m) Nh t).Z * (R.withMsq m).ℓ :=
    mul_pos (fscale_pos hZ) hℓ
  have hL0 : (0 : ℝ) < (L : ℝ) ^ (Nh + 1 + 1) :=
    pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hS : ∀ b' ∈ blockIdx (d := 2) (L := L) (N := N) (Nh + 1),
      ‖ε (Sb (Nh + 1) C (stVf (R.withMsq m) (Nh + 1) st (histOut (R.withMsq m) Nh t).g.re
        (histOut (R.withMsq m) Nh t).nu.re) (st.Wl + (histOut (R.withMsq m) Nh t).D) b' :
          Alg 2 L N)‖ ≤ w := fun b' hb' =>
    (abs_eps_le (E := Dir 2) (p := pPhi 2) hL0 hh _).trans (toReal_le_of hw0 (hB b' hb').2.2)
  rw [zUB_sub_u_eq R hNh m b μ₀ x, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  have hM : (blocks (Nh + 1) (univ : Finset (Lam 2 L N))).card ≤ L ^ 2 :=
    LastN.card_blockIdx_last (by omega)
  calc ∑ b' ∈ blocks (Nh + 1) (univ : Finset (Lam 2 L N)), ‖ε (LS (Nh + 1) C
          (stVf (R.withMsq m) (Nh + 1) st (histOut (R.withMsq m) Nh t).g.re
            (histOut (R.withMsq m) Nh t).nu.re) (st.Wl + (histOut (R.withMsq m) Nh t).D) b' :
          Alg 2 L N)‖
      ≤ ∑ _b' ∈ blocks (Nh + 1) (univ : Finset (Lam 2 L N)), (L : ℝ) ^ 2 * w :=
        sum_le_sum fun b' _ => PtCorr2.eps_LS_le (Nh + 1) C _ _ (by omega) hw0 hS b'
    _ = (blocks (Nh + 1) (univ : Finset (Lam 2 L N))).card * ((L : ℝ) ^ 2 * w) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (L : ℝ) ^ 2 * ((L : ℝ) ^ 2 * w) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast hM
    _ = (L : ℝ) ^ 4 * w := by ring

/-- Pure: comparing two factorisations of `⟨Z_0⟩` gives `s = U·e^{a − u}`. -/
theorem s_eq_of_fac {P d s U a u : ℂ} (hP : P ≠ 0) (hd : d ≠ 0)
    (h : P * (d * (Complex.exp (-a) * s)) = P * (d * Complex.exp (-u) * U)) :
    s = U * Complex.exp (a - u) := by
  have h1 : Complex.exp (-a) * s = Complex.exp (-u) * U := by
    have := mul_left_cancel₀ hP h
    rw [mul_assoc] at this
    exact mul_left_cancel₀ hd this
  have h2 : s = Complex.exp a * (Complex.exp (-u) * U) := by
    rw [← h1, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  rw [h2, sub_eq_add_neg, Complex.exp_add]; ring

/-- **The vertex at the two top scales, sharp form**: `‖β_{N_h}‖, ‖β_{N_h+1}‖ ≤ 2(1 + K_pG)bθ_{N_h}`
with `ǧ_{N_h−1} + a_{N_h−1} ≤ G` (`bt2_last_le` has `G = 3`). -/
theorem bt2_last_leG (P : Obs2.ObsPts 2 L N) {Nh : ℕ} (hNh : Nh + 2 = N) (h1 : 1 ≤ Nh)
    {m b μ₀ Kp cδ : ℝ} (hb : 0 < b) (hKp : 0 ≤ Kp)
    (hl : HLam R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) Kp)
    (hrel : Case2Rel R P (zV b) Nh m b μ₀ cδ)
    (hn : ‖nn2 R P (zV b) m b μ₀ (Nh - 1)‖ ≤ 1 / 8)
    (hg : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Nh - 1)).1)
    (hmono : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Nh - 1)).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hga0 : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Nh - 1)).1 + zA L m (Nh - 1))
    {G : ℝ} (hG0 : 0 ≤ G)
    (hga3 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Nh - 1)).1 + zA L m (Nh - 1) ≤ G)
    (htop : Case2TopStep R P (zV b) Nh m b μ₀) :
    ‖bt2 R P (zV b) m b μ₀ Nh‖ ≤ 2 * (1 + Kp * G) * b * thJ R m b μ₀ Nh ∧
      ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ ≤ 2 * (1 + Kp * G) * b * thJ R m b μ₀ Nh := by
  obtain ⟨k, rfl⟩ : ∃ k, Nh = k + 1 := ⟨Nh - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hn hg hmono hga0 hga3
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀
  -- the vertex at `k = N_h - 1`
  have hθk : 0 ≤ thJ R m b μ₀ k := Real.rpow_nonneg (div_nonneg hg hb.le) _
  have hθ : thJ R m b μ₀ k ≤ thJ R m b μ₀ (k + 1) :=
    Real.rpow_le_rpow (div_nonneg hg hb.le) (div_le_div_of_nonneg_right hmono hb.le) (by norm_num)
  have hlk := hl k (Nat.lt_succ_self _)
  have hlh : lamHat2 R P (zV b) m b μ₀ k = bt2 R P (zV b) m b μ₀ k / b := by
    unfold lamHat2; rw [bt2_zV_zero]
  rw [hlh] at hlk
  have hβk : ‖bt2 R P (zV b) m b μ₀ k‖ ≤ (1 + Kp * G) * b * thJ R m b μ₀ k := by
    have hβb : ‖bt2 R P (zV b) m b μ₀ k‖ = b * ‖bt2 R P (zV b) m b μ₀ k / b‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]; field_simp
    have h2 := norm_le_insert' (bt2 R P (zV b) m b μ₀ k / b) ((thJ R m b μ₀ k : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθk] at h2
    have hlk' : ‖bt2 R P (zV b) m b μ₀ k / b - ((thJ R m b μ₀ k : ℝ) : ℂ)‖ ≤
        Kp * thJ R m b μ₀ k * ((t k).1 + zA L m k) := hlk
    have h3 : Kp * thJ R m b μ₀ k * ((t k).1 + zA L m k) ≤ Kp * thJ R m b μ₀ k * G :=
      mul_le_mul_of_nonneg_left hga3 (mul_nonneg hKp hθk)
    have h4 : ‖bt2 R P (zV b) m b μ₀ k / b‖ ≤ (1 + Kp * G) * thJ R m b μ₀ k := by linarith
    rw [hβb]
    have := mul_le_mul_of_nonneg_left h4 hb.le
    linarith
  -- the step `N_h - 1 → N_h`
  have hf1 := bt2_flow R P (zV b) (Nh := k + 1) (by omega) m b μ₀ (k := k) (Nat.lt_succ_self _)
  obtain ⟨hr1, hr2⟩ := hrel k (Nat.lt_succ_self _)
  have hs1 : ‖bt2 R P (zV b) m b μ₀ (k + 1)‖ ≤ 81 / 64 * ‖bt2 R P (zV b) m b μ₀ k‖ := by
    rw [hf1]
    exact beta_step_le hn (hr1.trans (mul_le_mul_of_nonneg_right hr2 (norm_nonneg _)))
  -- the step `N_h → N_h + 1`
  have hf2 := bt2_flow R P (zV b) (Nh := k + 2) (by omega) m b μ₀ (k := k + 1) (by omega)
  have hs2 : ‖bt2 R P (zV b) m b μ₀ (k + 1 + 1)‖ ≤ 81 / 64 * ‖bt2 R P (zV b) m b μ₀ (k + 1)‖ := by
    rw [hf2]
    exact beta_step_le htop.1 htop.2
  have hX : 0 ≤ (1 + Kp * G) * b := mul_nonneg (by have := mul_nonneg hKp hG0; linarith) hb.le
  have hB : (1 + Kp * G) * b * thJ R m b μ₀ k ≤ (1 + Kp * G) * b * thJ R m b μ₀ (k + 1) :=
    mul_le_mul_of_nonneg_left hθ hX
  have hθ1 : 0 ≤ (1 + Kp * G) * b * thJ R m b μ₀ (k + 1) := mul_nonneg hX (hθk.trans hθ)
  have e : 2 * (1 + Kp * G) * b * thJ R m b μ₀ (k + 1) =
      2 * ((1 + Kp * G) * b * thJ R m b μ₀ (k + 1)) := by ring
  rw [e]
  constructor
  · linarith
  · linarith

/-- `1/|Z| ≤ e^{K_Zǧ}θ` from `|log|Z| + (1/3)log(ǧ/b)| ≤ K_Zǧ` (sharp form of `inv_normZ_le`). -/
theorem inv_normZ_leS {Z g b KZ : ℝ} (hZ : 0 < Z) (hg : 0 < g) (hb : 0 < b)
    (h : |Real.log Z + 1 / 3 * Real.log (g / b)| ≤ KZ * g) :
    Z⁻¹ ≤ Real.exp (KZ * g) * (g / b) ^ (1 / 3 : ℝ) := by
  rw [Real.rpow_def_of_pos (div_pos hg hb), ← Real.exp_add, ← Real.exp_log hZ, ← Real.exp_neg]
  refine Real.exp_le_exp.2 ?_
  have h1 := (abs_le.1 h).1
  linarith

set_option maxHeartbeats 1000000 in
/-- **`γ_{a,N}` near `ϑ_{N_h}`** (one trajectory; the inputs of `gamTopBd_of` without the
smallness): `‖γ_{a,N} − ϑ_{N_h}‖ ≤ (max(f(K_p + c_γ), 0) + c_L)ϑ_{N_h}ǧ_{N_h}`. -/
theorem gamNa_near_of (hP : R.P = Pc) {Nh : ℕ} {m b μ₀ : ℝ} {f : ℝ → ℝ}
    (hMag : MagAt R Nh m b μ₀ f) (hm : 0 ≤ m) (hb : 0 < b)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i)
    (hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (ha : ∀ k < Nh, zA L m k ≤ 2)
    {Kp ce cw cL : ℝ} (hKp : 0 ≤ Kp) (hce : 0 ≤ ce) (hcw : 0 ≤ cw)
    (hpair : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp)
    (hB : GamBulkRel R Nh m b μ₀ ce) (hW : GamWKTop R Nh m b μ₀ cw)
    (hLast : GamLastRel R Nh m b μ₀ cL) (x : Lam 2 L N) (hx : x ≠ 0)
    (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x) (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) :
    ‖gamNa R Nh m b μ₀ x - ((varthJ R m b μ₀ Nh : ℝ) : ℂ)‖ ≤
      (max (f (Kp + (ce + cw) * (1 + 3 * Kp))) 0 + cL) * varthJ R m b μ₀ Nh *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by
  set cγ := (ce + cw) * (1 + 3 * Kp) with hcγd
  have hcγ : 0 ≤ cγ := mul_nonneg (add_nonneg hce hcw) (by linarith)
  have hNh : 1 ≤ Nh := h1.trans hj
  have hrem := gamRemX_top_le R hb hKp hce hcw hV
    (fun k hk => ⟨(hg k hk.le).1.le, (hg k hk.le).2⟩)
    (fun k hk => ⟨zA_nonneg L hm k, ha k hk⟩) (hpair x hx) hB (hW x hx h1 hj)
  have hθa : ∀ k < Nh, 0 ≤ thJ R m b μ₀ k *
      ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) := fun k hk =>
    mul_nonneg (Real.rpow_nonneg (div_pos (hg k hk.le).1 hb).le _)
      (add_nonneg (hg k hk.le).1.le (zA_nonneg L hm k))
  have hlG := hLam_lamG R hb hcγ (hpair x hx) hθa hrem
  have h0 : ∀ k < Nh, gamT R m b μ₀ k = 0 → gamRemX R m b μ₀ x k = 0 := by
    intro k hk hΓ
    have := hrem k hk
    rw [hΓ, norm_zero, mul_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  have hU := uA_eq_mmag R hP hb.ne' x hNh h0
  have hKp' : 0 ≤ Kp + cγ := add_nonneg hKp hcγ
  have hM' := hMag (lamG R m b μ₀ x) (Kp + cγ) hKp' hlG Nh le_rfl
  have hGU : ‖gamNa R Nh m b μ₀ x - uA R m b μ₀ x Nh‖ ≤
      cL * varthJ R m b μ₀ Nh * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by
    rw [gamNa_sub_uA R hP hNh]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg]; exact hLast x hx h1 hj
  have hv' : 0 ≤ varthJ R m b μ₀ Nh := Real.rpow_nonneg (div_pos hb (hg Nh le_rfl).1).le _
  have hM'' : ‖Mmag R m b μ₀ (lamG R m b μ₀ x) Nh - ((varthJ R m b μ₀ Nh : ℝ) : ℂ)‖ ≤
      max (f (Kp + cγ)) 0 * varthJ R m b μ₀ Nh * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 :=
    hM'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hv')
      (hg Nh le_rfl).1.le)
  rw [hU] at hGU
  have := norm_sub_le_norm_sub_add_norm_sub (gamNa R Nh m b μ₀ x)
    (Mmag R m b μ₀ (lamG R m b μ₀ x) Nh) ((varthJ R m b μ₀ Nh : ℝ) : ℂ)
  have e : (max (f (Kp + cγ)) 0 + cL) * varthJ R m b μ₀ Nh *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 =
      max (f (Kp + cγ)) 0 * varthJ R m b μ₀ Nh * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 +
        cL * varthJ R m b μ₀ Nh * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by ring
  rw [e]; linarith

end Traj

end

end Spin2
