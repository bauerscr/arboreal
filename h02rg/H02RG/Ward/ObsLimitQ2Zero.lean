import Ward.ObsLimitQ2
import Ward.ObsLimitQ1Zero
import Ward.ObsLimitP

/-!
# The value of `Q2` at `m² = 0`

`Qtwo_zero_add_green`: for `x ∈ ℤ^d ∖ {0}` and `|b₀| ≤ λ̄`,
`|Q2(x)(0, b₀) + Λ(0, b₀)^2 G_{ℤ^d}(x)^2| ≤ K |b₀| |x|_∞^{-(2(d-2)+κ)}`,
with `Λ = LamA` (by `LamA_eq_LamB` the `b` slot coupling at `m² = 0` is also `LamA`).

Proof: `PtCorr.flowTwo_core` at `m² = 0` gives, uniformly in `N`,
`|q_N + λ_{a,N} λ_{b,N} (∑_{k<N} C_{k+1}(a,b))^2| ≤ K_2 e ℓ_{j_ab}^4 θ^{j_ab}`; then `N → ∞`
with `qN2_rate`, `lamA2_rate`, `lamB2_rate` + `LamA_eq_LamB`, `covsum_tendsto`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Metric Filter Topology

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

variable (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) (hd : 1 ≤ d) {Cs Cq Cb : ℝ} (hCs : 0 ≤ Cs)
  (hS : StepBd d L A ℓ₀ V₀c lbar C κ Cs) (hCq : 0 ≤ Cq) (hCb : 0 ≤ Cb)
  (hP : PairHyp2 d L A ℓ₀ V₀c lbar C κ Cq Cb)
include H hd hCs hS hCq hCb hP

/-- **`Q2(x) = -Λ^2 G_{ℤ^d}(x)^2 + O(|b₀| |x|^{-(2(d-2)+κ)})` at `m² = 0`**. -/
theorem Qtwo_zero_add_green (hd3 : 3 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (b₀ : ℂ), ‖b₀‖ ≤ lbar →
    ∀ x : Zd d, x ≠ 0 →
      ‖Qtwo d L V₀c lbar 0 b₀ x + LamA d L V₀c lbar 0 b₀ ^ 2 * (greenZd d x : ℂ) ^ 2‖ ≤
        K * ‖b₀‖ * (supNormZ x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)) := by
  have hd2 : 2 ≤ d := by omega
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  have hlb := H.fd.lbar_pos
  have hC0 := H.fd.C_nonneg
  have hκ := H.fd.κ_pos
  have hθ0 := th_nonneg L κ
  have hθ1 := th_lt_one hL2 hκ (L := L)
  obtain ⟨Cs2, hCs2, hcore⟩ := flowTwo_core hd3
  have hKT : 0 ≤ KTwo Cs2 (th L κ) lbar (C * lbar * lbar) :=
    KTwo_nonneg hCs2 hθ1 hlb.le (by positivity)
  refine ⟨KTwo Cs2 (th L κ) lbar (C * lbar * lbar) * C / lbar *
    (ℓ₀ ^ 4 * (L : ℝ) ^ (2 * ((d : ℝ) - 2) + κ)), by positivity, ?_⟩
  intro b₀ hb₀ x hx0
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = Nat.log L (2 * supNormZ x) := ⟨_, rfl⟩
  have hlb2 : 0 < lbar ^ 2 := by positivity
  have hl : (lbar : ℂ) ≠ 0 := by exact_mod_cast hlb.ne'
  have hl1 := norm_lbar H
  have hE : 0 ≤ C * lbar * ‖b₀‖ := by positivity
  have hEb : C * lbar * ‖b₀‖ ≤ C * lbar * lbar := mul_le_mul_of_nonneg_left hb₀ (by positivity)
  -- the finite-`N` bound
  have hN_bd : ∀ N : ℕ, 2 + supNormZ x ≤ N →
      ‖qN d L .two N 0 (V₀c 0 b₀) (initObs .two (lbar : ℂ)) (ctr d L N) (ctr d L N + prj x) +
          laOf .two (VoN d L .two N 0 (V₀c 0 b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
            (ctr d L N + prj x)) *
          lbOf .two (VoN d L .two N 0 (V₀c 0 b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
            (ctr d L N + prj x)) *
          (∑ k ∈ range N, (Flow.covAt d L N 0 k (ctr d L N) (ctr d L N + prj x) : ℂ)) ^ 2‖ ≤
        KTwo Cs2 (th L κ) lbar (C * lbar * lbar) * (C * lbar * ‖b₀‖) *
          (ℓ₀ ^ 4 * ((L : ℝ) ^ (2 * ((d : ℝ) - 2) + κ) *
            (supNormZ x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)))) := by
    intro N hN
    have hs : supNormZ x ≤ L ^ (N - 1) := by
      have h1 : supNormZ x < L ^ supNormZ x := Nat.lt_pow_self (by omega)
      have h2 : L ^ supNormZ x ≤ L ^ (N - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have h2s := two_s_lt hL3 hs (by omega)
    have hb := ctr_add_prj_ne hL3 (N := N) (by omega) hx0 hs
    have hsn : supNorm (ctr d L N - (ctr d L N + prj x)) = supNormZ x := by
      rw [show ctr d L N - (ctr d L N + prj x) = -prj x by abel, supNorm_neg, supNorm_prj_of h2s]
    have hcoal : coal L (ctr d L N) (ctr d L N + prj x) = c := by rw [coal, hsn, hc]
    have hK : ∀ k ≤ N, KnormObs .two ℓ₀ (ctr d L N) (ctr d L N + prj x) k A
        (flowO d L .two N 0 (V₀c 0 b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
          (ctr d L N + prj x) k).2 ≤ ENNReal.ofReal (C * lbar * ‖b₀‖ * th L κ ^ k) := by
      intro k hk
      have := (H.fd.obs .two N 0 (lbar : ℂ) b₀ (ctr d L N + prj x) le_rfl
        (by rw [hl1]; exact hb₀) (le_of_eq hl1) hb k hk).2
      rwa [hl1, rpow_neg_mul_nat (Nat.cast_nonneg _) κ k] at this
    obtain ⟨-, -, -, -, -, hq, -, -⟩ := hcore L H.fd.hL8 N 0 (V₀c 0 b₀) ℓ₀ H.fd.hℓ₀
      (H.fd.good N 0 le_rfl) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x) A H.fd.hA1 (th L κ)
      (C * lbar * ‖b₀‖) lbar (C * lbar * lbar) hθ0 hθ1 hE (le_of_eq hl1) hEb hK
    rw [hcoal] at hq
    refine hq.trans ?_
    have hconv := ellj_coal_pow_four_mul_pow_le hd2 hL2 ℓ₀ (s := κ) hκ.le (Ne.symm hb)
    rw [hcoal, hsn] at hconv
    exact mul_le_mul_of_nonneg_left hconv (by positivity)
  -- the limits
  have ev : ∀ᶠ N : ℕ in atTop, 2 + supNormZ x ≤ N ∧ supNormZ x ≤ L ^ (N - 1) ∧
      (prj x : Lam d L N) ≠ 0 := by
    filter_upwards [eventually_ge_atTop (2 + supNormZ x)] with N hN
    have hs : supNormZ x ≤ L ^ (N - 1) := by
      have h1 : supNormZ x < L ^ supNormZ x := Nat.lt_pow_self (by omega)
      have h2 : L ^ supNormZ x ≤ L ^ (N - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    exact ⟨hN, hs, prj_ne_zero hx0 (two_s_lt hL3 hs (by omega))⟩
  have hQ : Tendsto (fun N => qN d L .two N 0 (V₀c 0 b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
      (ctr d L N + prj x) / (lbar : ℂ) ^ 2) atTop (𝓝 (Qtwo d L V₀c lbar 0 b₀ x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have ht := (tendsto_rpow_neg_mul (L := L) hL2 (s := (d : ℝ) - 2)
        (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd3); linarith)).const_mul
        (Kq2 lbar C κ Cs Cq Cb ℓ₀ b₀ L * (1 + 1 / (1 - rho d L)) / (rho d L * lbar ^ 2))
    rw [mul_zero] at ht
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ ht
    filter_upwards [ev] with N hN
    exact qN2_rate H hd hCs hS hCq hCb hP hd3 le_rfl hb₀ hx0 (by omega) hN.2.1
  have hlA : Tendsto (fun N => lamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) (prj x : Lam d L N)) atTop
      (𝓝 (LamA d L V₀c lbar 0 b₀)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have ht := (tendsto_rpow_neg_mul (L := L) hL2 hκ).const_mul
      (2 * Cs * C / (th L κ ^ 2 * (1 - th L κ)) * ‖b₀‖)
    rw [mul_zero] at ht
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ ht
    filter_upwards [ev] with N hN
    exact lamA2_rate H hd hCs hS le_rfl hb₀ (by omega) hN.2.2
  have hlB : Tendsto (fun N => lamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) (prj x : Lam d L N)) atTop
      (𝓝 (LamA d L V₀c lbar 0 b₀)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have ht := (tendsto_rpow_neg_mul (L := L) hL2 hκ).const_mul
      (2 * Cs * C / (th L κ ^ 2 * (1 - th L κ)) * ‖b₀‖)
    rw [mul_zero] at ht
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ ht
    filter_upwards [ev] with N hN
    have := lamB2_rate H hd hCs hS le_rfl hb₀ (by omega) hN.2.2
    rwa [← LamA_eq_LamB H hd hCs hS hd3 hb₀ (redZ_nonneg _ _)] at this
  have hG := covsum_tendsto H hd hd3 x
  have hlim := (hQ.add ((hlA.mul hlB).mul (hG.pow 2))).norm
  rw [← sq] at hlim
  refine le_of_tendsto hlim ?_
  filter_upwards [ev] with N hN
  have e : qN d L .two N 0 (V₀c 0 b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
        (ctr d L N + prj x) / (lbar : ℂ) ^ 2 +
      lamA2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) (prj x : Lam d L N) *
        lamB2 d L N 0 (V₀c 0 b₀) (lbar : ℂ) (prj x : Lam d L N) *
        (∑ k ∈ range N, (Flow.covAt d L N 0 k (ctr d L N) (ctr d L N + prj x) : ℂ)) ^ 2 =
      (qN d L .two N 0 (V₀c 0 b₀) (initObs .two (lbar : ℂ)) (ctr d L N) (ctr d L N + prj x) +
          laOf .two (VoN d L .two N 0 (V₀c 0 b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
            (ctr d L N + prj x)) *
          lbOf .two (VoN d L .two N 0 (V₀c 0 b₀) (initObs .two (lbar : ℂ)) (ctr d L N)
            (ctr d L N + prj x)) *
          (∑ k ∈ range N, (Flow.covAt d L N 0 k (ctr d L N) (ctr d L N + prj x) : ℂ)) ^ 2) /
        (lbar : ℂ) ^ 2 := by
    rw [lamA2, lamB2]; field_simp
  rw [e, norm_div, norm_pow, hl1, div_le_iff₀ hlb2]
  refine (hN_bd N hN.1).trans (le_of_eq ?_)
  field_simp

end

end Ward
