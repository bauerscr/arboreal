import Spin2.Case2.Case2Rel
import PtCorr2.Obs.ConstSplitHist
import Spin2.Gam.GamBulk2
import Spin2.Gam.GamTop
import PtCorr2.Obs.GamWKBd

-- Merged from `Spin2/Case2RelPair.lean` (phase 3).
section

/-!
# `Case2Rel` for Case-(2) vertices with `γ_a ≠ 0` (in particular the pair vertex `zV b`)

Route (i) of the `γ_a ≠ 0` obstruction: the observable constant `−γ_aσ_a` of `V_0(B)` is a
scalar of the field algebra and decouples exactly (`Obs2.Map.ConstSplit`,
`PtCorr2.Obs.ConstSplitHist`): along every trajectory (`K_0 = 0`) the couplings `β_k`, the one-loop
coefficients `𝔫^{(2)}_k`, the errors `err_k` and the `K`/`𝒲` part of `ρ_k` of `V` are those of
`gaZero V` (`γ_a = 0`), at every scale (`bt2_gaZero`, `nn2_gaZero`, `err2_gaZero`, `lamHat2_gaZero`,
`gamWK2_traj_gaZero`). Hence

* `case2Rel_gaZero_iff`, `case2Loop_gaZero_iff`;
* **`RelConcl2G`** (`Case2Rel` for every Case-(2) vertex with `μ_a ≠ 0`, any `γ_a`) from
  `RelConcl2` (`relConcl2G_of`), so `thm_multiscale_case2D`'s constants give `Case2Rel` at the
  pair vertex `zV b` (`γ = 1`, `μ = −b`) at `ptsX x` and `ptsS x`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2.D2

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two)

theorem traj_zero_X (m b μ₀ : ℝ) : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ 0).2.2 = 0 := rfl

theorem bt2_gaZero (m b μ₀ : ℝ) (k : ℕ) :
    bt2 R P V m b μ₀ k = bt2 R P (PtCorr2.gaZero V) m b μ₀ k :=
  PtCorr2.betaTot2_gaZero (R.withMsq m) P V (traj_zero_X R m b μ₀) k

theorem nn2_gaZero (m b μ₀ : ℝ) (k : ℕ) :
    nn2 R P V m b μ₀ k = nn2 R P (PtCorr2.gaZero V) m b μ₀ k :=
  PtCorr2.frakN2_gaZero (R.withMsq m) P V (traj_zero_X R m b μ₀) k

theorem err2_gaZero (m b μ₀ : ℝ) (k : ℕ) :
    err2 R P V m b μ₀ k = err2 R P (PtCorr2.gaZero V) m b μ₀ k := by
  unfold err2
  exact sum_congr rfl fun c' _ =>
    PtCorr2.shareErr2_gaZero (R.withMsq m) P V (traj_zero_X R m b μ₀) k _

theorem gamWK2_traj_gaZero (m b μ₀ : ℝ) (k : ℕ) :
    Obs2.gamWK2 (R.withMsq m) P (Obs2.obsInit .two V P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k =
      Obs2.gamWK2 (R.withMsq m) P (Obs2.obsInit .two (PtCorr2.gaZero V) P)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k :=
  PtCorr2.gamWK2_gaZero (R.withMsq m) P V (traj_zero_X R m b μ₀) k

theorem case2Rel_gaZero_iff (Nh : ℕ) (m b μ₀ cδ : ℝ) :
    Case2Rel R P V Nh m b μ₀ cδ ↔ Case2Rel R P (PtCorr2.gaZero V) Nh m b μ₀ cδ := by
  unfold Case2Rel
  simp only [err2_gaZero R P V, bt2_gaZero R P V, nn2_gaZero R P V]

/-- **`Case2Rel` along every admissible trajectory for every Case-(2) vertex with `μ_a ≠ 0`**
(any `γ_a`). -/
def RelConcl2G (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cδ : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two),
    Obs2.OCoup2.mua V ≠ 0 → Case2Rel R P V Nh m b μ₀ cδ

/-- **`RelConcl2` (`γ_a = 0`) gives `Case2Rel` for every `γ_a`.** -/
theorem relConcl2G_of {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε cδ : ℝ}
    (h : RelConcl2 L ℓ A ρ κ cm cT ε cδ) : RelConcl2G L ℓ A ρ κ cm cT ε cδ := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P V hmu
  rw [case2Rel_gaZero_iff]
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm P (PtCorr2.gaZero V) rfl hmu

end

end Spin2

end

/-!
# The pair vertex: `Case2Rel`, `GamWKRel`, `GamWKRelS`, `GamWKTop`, and `TwoPtSq`

Under one set of master constants (`thm_flow_master_all` with the requirements of
`thm_multiscale_case2D` and of `thm_gam_bulk`):

* **`RelConcl2G`**: `Case2Rel` for every Case-(2) vertex with `μ_a ≠ 0`, any `γ_a`
  (`relConcl2G_of`: the constant `γ_a` decouples exactly, `Obs2.Map.ConstSplit`);
* **`WKConcl c_w`**: for every point configuration `P`, every vertex with `μ_a ≠ 0` and every
  `k < N_h`: `‖gamWK2_k‖ ≤ c_w(ǧ_k + a_k)‖β_k‖‖Γ^{int}_{k+1}(0,0)‖`
  (`gamWK2_k` of `V` is that of `gaZero V`; for `γ_a = 0`, `PtCorr2.obs_hist_rel2_base` gives
  `‖𝒲^{obs}_k(B)‖ ≤ c_Wr_k·2s_k²|β_k|`, `K^{obs}_k ≲ r_k²s_k²|β_k|`; `PtCorr2.gamWK2_le` turns them
  into `|gamWK2_k| ≲ r_k|β_k|(s_k² + |C_k(a,a)|)`; `C_k(a,a) = Γ^{int}_{k+1}(0,0)`,
  `s_k² ≤ (9/8)ℓ²|Γ^{int}_{k+1}(0,0)|` from `C2Ctx.gamInt_lower` (`k ≥ 1`), `gamWK2_0 = 0`);
* `GamBulkConcl` (as in `thm_gam_bulk`);
* corollaries (`wk_inputs`): `GamWKRel`, `GamWKRelS`, `GamWKTop`, and the mirrored all-`k` bound
  (`gamWKMir`, for `GamWKTopS`);
* **`twoPtSq_case2_pair`**: `twoPtSq_of_gam_flow3` without the inputs (H_λ) for the pair vertices
  at `ptsX x`, `ptsS x`, `GamWKRel`, `GamWKRelS`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L N : ℕ} [NeZero L]

/-! ### Pure facts -/

theorem wk_alg {T kk w s G r b c cW Bk cN cB Q D g a : ℝ}
    (hT : T ≤ cN * (8 * kk) + G * (cN * (8 * kk) * s⁻¹ ^ 2) + cB * (Q * w))
    (hkk : kk = 16 * cW * Bk * r ^ 2 * (s ^ 2 * b)) (hw : w = cW * r * (2 * s ^ 2 * b))
    (hs : 0 < s) (hsG : s ^ 2 ≤ D * G) (hr : r = c * g) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hcN : 0 ≤ cN) (hcW : 0 ≤ cW) (hBk : 0 ≤ Bk)
    (hcB : 0 ≤ cB) (hQ : 0 ≤ Q) (hb : 0 ≤ b) (hG : 0 ≤ G) :
    T ≤ c * (128 * cN * cW * Bk * (D + 1) + 2 * cB * Q * cW * D) * (g + a) * b * G := by
  have hs2 : s ^ 2 * s⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hs.ne', one_pow]
  have hr2 : r ^ 2 ≤ r := by nlinarith
  set E := cN * cW * Bk * b with hE
  have hE0 : 0 ≤ E := by positivity
  have h1 : cN * (8 * kk) ≤ 128 * cN * cW * Bk * D * (r * b * G) := by
    rw [hkk]
    have : cN * (8 * (16 * cW * Bk * r ^ 2 * (s ^ 2 * b))) = 128 * E * (r ^ 2 * s ^ 2) := by
      rw [hE]; ring
    rw [this]
    have h := mul_le_mul hr2 hsG (sq_nonneg s) hr0
    have e : 128 * cN * cW * Bk * D * (r * b * G) = 128 * E * (r * (D * G)) := by rw [hE]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : G * (cN * (8 * kk) * s⁻¹ ^ 2) ≤ 128 * cN * cW * Bk * (r * b * G) := by
    rw [hkk]
    have : G * (cN * (8 * (16 * cW * Bk * r ^ 2 * (s ^ 2 * b))) * s⁻¹ ^ 2) =
        128 * E * G * r ^ 2 * (s ^ 2 * s⁻¹ ^ 2) := by rw [hE]; ring
    rw [this, hs2, mul_one]
    have e : 128 * cN * cW * Bk * (r * b * G) = 128 * E * G * r := by rw [hE]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hr2 (by positivity)
  have h3 : cB * (Q * w) ≤ 2 * cB * Q * cW * D * (r * b * G) := by
    rw [hw]
    have : cB * (Q * (cW * r * (2 * s ^ 2 * b))) = (2 * cB * Q * cW * r * b) * s ^ 2 := by ring
    rw [this]
    have e : 2 * cB * Q * cW * D * (r * b * G) = (2 * cB * Q * cW * r * b) * (D * G) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hsG (by positivity)
  have hD : 0 ≤ D := by
    by_contra hneg
    have : D * G ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.1 hneg)) hG
    have : 0 < s ^ 2 := by positivity
    linarith
  have hg : 0 ≤ g ∨ c = 0 := by
    rcases eq_or_lt_of_le hc with h | h
    · exact Or.inr h.symm
    · left; rw [hr] at hr0; exact nonneg_of_mul_nonneg_right (by linarith [hr0]) h
  have h4 : r * b * G ≤ c * (g + a) * b * G := by
    rw [hr]
    have : c * g ≤ c * (g + a) := mul_le_mul_of_nonneg_left (by linarith) hc
    have hbG : 0 ≤ b * G := mul_nonneg hb hG
    nlinarith
  have e : c * (128 * cN * cW * Bk * (D + 1) + 2 * cB * Q * cW * D) * (g + a) * b * G =
      (128 * cN * cW * Bk * D + 128 * cN * cW * Bk + 2 * cB * Q * cW * D) *
        (c * (g + a) * b * G) := by ring
  rw [e]
  have hKp : 0 ≤ 128 * cN * cW * Bk * D + 128 * cN * cW * Bk + 2 * cB * Q * cW * D := by
    positivity
  have h5 := mul_le_mul_of_nonneg_left h4 hKp
  have e2 : (128 * cN * cW * Bk * D + 128 * cN * cW * Bk + 2 * cB * Q * cW * D) * (r * b * G) =
      128 * cN * cW * Bk * D * (r * b * G) + 128 * cN * cW * Bk * (r * b * G) +
        2 * cB * Q * cW * D * (r * b * G) := by ring
  linarith

/-- **`s_k² ≤ (9/8)ℓ²|Γ^{int}_{k+1}(0,0)|`** from `|Z_{k+1}Γ^{int}_{k+1}(0,0)| ≥ 1`. -/
theorem histS_sq_le_gam (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (t : Hist.Seq (Xs R)) (k : ℕ) (hρ0 : 0 ≤ R.ρ) (hρ8 : R.ρ ≤ 1 / 8)
    (hZ : (rawHist R k t).Z ≠ 0) (hlow : 1 ≤ zH R t (k + 1) * ‖GamInt R k t‖) :
    histS R k t ^ 2 ≤ 9 / 8 * R.ℓ ^ 2 * ‖GamInt R k t‖ := by
  have hZ0 : 0 < ‖(rawHist R k t).Z‖ := norm_pos_iff.2 hZ
  have hζ : ‖zetaH R k t‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ8
  have hZ1 : zH R t (k + 1) ≤ 9 / 8 * ‖(rawHist R k t).Z‖ := by
    show ‖(rawHist R (k + 1) t).Z‖ ≤ _
    rw [rawHist_succ_Z, norm_mul]
    have : ‖1 + zetaH R k t‖ ≤ 9 / 8 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
    nlinarith
  have hG := norm_nonneg (GamInt R k t)
  have h1 : 1 ≤ 9 / 8 * ‖(rawHist R k t).Z‖ * ‖GamInt R k t‖ :=
    hlow.trans (mul_le_mul_of_nonneg_right hZ1 hG)
  have e : histS R k t ^ 2 = R.ℓ ^ 2 * ‖(rawHist R k t).Z‖⁻¹ := by
    unfold histS; rw [mul_pow, fscale_sq]; ring
  rw [e]
  have h2 : ‖(rawHist R k t).Z‖⁻¹ ≤ 9 / 8 * ‖GamInt R k t‖ := by
    rw [inv_le_iff_one_le_mul₀ hZ0]; nlinarith
  have := mul_le_mul_of_nonneg_left h2 (sq_nonneg R.ℓ)
  linarith

/-! ### The conclusion -/

/-- **The `K`/`𝒲` part of `ρ_k` relative to the vertex**, along every admissible trajectory, for
every point configuration and every Case-(2) vertex with `μ_a ≠ 0`, at every `k < N_h`. -/
def WKConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cw : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two), Obs2.OCoup2.mua V ≠ 0 →
  ∀ k < Nh, ‖Obs2.gamWK2 (R.withMsq m) P (Obs2.obsInit .two V P)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k‖ ≤
    cw * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) * ‖bt2 R P V m b μ₀ k‖ *
      ‖gamT R m b μ₀ k‖

theorem zV_mua_ne {b : ℝ} (hb : 0 < b) : Obs2.OCoup2.mua (zV b) ≠ 0 := by
  show -(b : ℂ) ≠ 0
  rw [neg_ne_zero]; exact_mod_cast hb.ne'

/-- **`GamWKRel`, `GamWKRelS`, `GamWKTop` and the mirrored all-`k` bound from `WKConcl`.** -/
theorem wk_inputs {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε cw : ℝ} (hW : WKConcl L ℓ A ρ κ cm cT ε cw)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = ℓ) (hRA : R.A = A) (hRρ : R.ρ = ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hadm : Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀) :
    GamWKRel R Nh m b μ₀ cw ∧ GamWKRelS R Nh m b μ₀ cw ∧ GamWKTop R Nh m b μ₀ cw ∧
      ∀ x : Lam 2 L N, ∀ k < Nh, ‖gamWKMir R m b μ₀ x k‖ ≤
        cw * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) * ‖btMir R m b μ₀ x k‖ *
          ‖gamT R m b μ₀ k‖ := by
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have H := hW N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  refine ⟨fun x _ hj k hk => H (ptsX x) (zV b) (zV_mua_ne hb) k (lt_of_lt_of_le hk hj),
    fun x _ hj k hk => H (ptsS x) (zV b) (zV_mua_ne hb) k (lt_of_lt_of_le hk hj),
    fun x _ _ _ k hk => H (ptsX x) (zV b) (zV_mua_ne hb) k hk,
    fun x k hk => H (ptsS x) (zV b) (zV_mua_ne hb) k hk⟩

end

end Spin2
