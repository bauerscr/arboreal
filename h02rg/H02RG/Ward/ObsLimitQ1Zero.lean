import Ward.ObsLimitQ1
import Ward.ObsLimitZero
import PtCorr.TwoPtOne

/-!
# Infinite-volume limits: the value of `Q1` at `m² = 0`

`Qone_zero_sub_green`: for `x ∈ ℤ^d ∖ {0}` and `|b₀| ≤ λ̄`,
`|Q1(x)(0, b₀) - G_{ℤ^d}(x)| ≤ K |b₀| |x|_∞^{-(d-2+κ)}`.

Proof, at finite `N` and `m² = 0` on `Λ_N` at `(ctr_N, ctr_N + x)`:
* the Case (1) `λ` tails `|λ_{x,j} - λ̄| ≤ C_l λ̄ |b₀| L^{-κj}` (`PtCorr.lamOne_of`, `m² > 0`)
  extend to `m² = 0` by continuity (`laOne_zero`);
* `PtCorr.qN_sub_le_one` then gives `|q_N - λ̄² ∑_{k<N} C_{k+1}(a,b)| ≤ M ℓ_{j_ab}^2 θ^{j_ab}`
  with `M = O(|b₀|)` uniform in `N`;
* at `m² = 0`, `C_{k+1}(a, b) = c_{k+1}(-x)` of `ℤ^d` for `k + 2 ≤ N` and `|C_N(a,b)| ≤ ℓ_N^2`,
  so `∑_{k<N} C_{k+1}(a,b) → G_{ℤ^d}(-x) = G_{ℤ^d}(x)`; with `qN_rate` and `N → ∞`;
* `ℓ_{j_ab}^2 θ^{j_ab} ≤ ℓ₀^2 L^{d-2+κ} |x|^{-(d-2+κ)}` (`PtCorr.ellj_coal_sq_mul_pow_le`).
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Metric Filter Topology

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

theorem greenZd_neg (z : Zd d) : greenZd d (-z) = greenZd d z := by
  unfold greenZd
  congr 2
  funext k
  congr 1
  rw [show ∑ i, k i * ((-z) i : ℤ) = -∑ i, k i * (z i : ℝ) by
    simp [Finset.sum_neg_distrib]]
  exact Real.cos_neg _

theorem rep_prj_of {N : ℕ} {x : Zd d} (hs : 2 * supNormZ x < L ^ N) :
    rep (prj x : Lam d L N) = x := (eq_rep rfl hs).symm

theorem supNorm_prj_of {N : ℕ} {x : Zd d} (hs : 2 * supNormZ x < L ^ N) :
    supNorm (prj x : Lam d L N) = supNormZ x := by
  unfold supNorm supNormZ
  congr 1
  funext i
  rw [← natAbs_rep, rep_prj_of hs]

/-- At `m² = 0`, the covariance of step `k`, `k + 2 ≤ N`, between `ctr` and `ctr + x` is the
`ℤ^d` covariance `c_{k+1}(-x)`. -/
theorem covAt_pair_zero (hd : 1 ≤ d) (hL : 2 ≤ L) {N k : ℕ} (hk : k + 2 ≤ N) {x : Zd d}
    (hs : 2 * supNormZ x < L ^ N) (a : Lam d L N) :
    Flow.covAt d L N 0 k a (a + prj x) =
      covZ stdPt d 0 (Set.Ioc (lowEnd (L : ℝ) (k + 1)) ((L : ℝ) ^ (k + 1) / 2)) (-x) := by
  rw [Flow.covAt_lt (by omega)]
  show Cj stdPt 0 (L : ℝ) (k + 1) a (a + prj x) = _
  have hn : (L : ℝ) ^ (k + 1) < ((L ^ N : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_lt_pow_right (by omega) (by omega)
  rw [Cj_eq_Zd stdPt le_rfl hd (Nat.cast_nonneg _) (k + 1) hn, show a - (a + prj x) = prj (-x) by
    rw [FRD.prj_neg]; abel]
  rw [rep_prj_of (by rw [Loc.supNormZ_neg]; exact hs)]

variable (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) (hd : 1 ≤ d) {Cs : ℝ} (hCs : 0 ≤ Cs)
  (hS1 : StepBd1 d L A ℓ₀ V₀c lbar C κ Cs)
include H hd hCs hS1

/-- **Case (1) `λ` tails at `m² = 0`**. -/
theorem laOne_zero (hd3 : 3 ≤ d) : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ (N : ℕ) (b₀ : ℂ) (b : Lam d L N),
    ‖b₀‖ ≤ lbar → b ≠ ctr d L N → ∀ j ≤ N,
      ‖laOne d L N 0 (V₀c 0 b₀) (lbar : ℂ) (ctr d L N) b j - lbar‖ ≤
          Cl * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) ∧
        ‖lbOne d L N 0 (V₀c 0 b₀) (lbar : ℂ) (ctr d L N) b j - lbar‖ ≤
          Cl * lbar * ‖b₀‖ * (L : ℝ) ^ (-(κ * j)) := by
  obtain ⟨Cl, hCl, h⟩ := PtCorr.lamOne_of hd3 H.fd
  refine ⟨Cl, hCl, fun N b₀ b hb₀ hb j hj => ?_⟩
  have hl := norm_lbar H
  have hpos := fun m (hm : 0 < m) => h N m (lbar : ℂ) b₀ b hm (by rw [hl]; exact hb₀)
    (le_of_eq hl) hb j hj
  have hlim : ∀ {f : ℝ → ℂ}, ContinuousOn f (Set.Ici 0) → Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
    fun hf => (hf 0 Set.self_mem_Ici).tendsto.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hA := hlim (H.fd.laOne_cont hd hb₀ (lbar : ℂ) (ctr d L N) b hj)
  have hB := hlim (H.fd.lbOne_cont hd hb₀ (lbar : ℂ) (ctr d L N) b hj)
  rw [hl] at hpos
  refine ⟨le_of_tendsto (hA.sub_const _).norm ?_, le_of_tendsto (hB.sub_const _).norm ?_⟩ <;>
  · filter_upwards [self_mem_nhdsWithin] with m hm
    first
    | exact (hpos m hm).1
    | exact (hpos m hm).2

omit hCs hS1 in
/-- At `m² = 0`, `∑_{k<N} C_{k+1}(ctr_N, ctr_N + x) → G_{ℤ^d}(x)`. -/
theorem covsum_tendsto (hd3 : 3 ≤ d) (x : Zd d) :
    Tendsto (fun N => ∑ k ∈ range N, (Flow.covAt d L N 0 k (ctr d L N)
      (ctr d L N + prj x) : ℂ)) atTop (𝓝 (greenZd d x : ℂ)) := by
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  have hsum := hasSum_covZ_green stdPt hd3 (by exact_mod_cast (by omega : 1 < L) : (1 : ℝ) < L)
    (-x)
  rw [greenZd_neg] at hsum
  have ht := (Complex.hasSum_ofReal.2 hsum).tendsto_sum_nat
  have hlast : Tendsto (fun N : ℕ => (Flow.covAt d L N 0 (N - 1) (ctr d L N)
      (ctr d L N + prj x) : ℂ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ?_ (a := fun N : ℕ => ℓ₀ ^ 2 * rho d L ^ N)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have := abs_cov_le H.fd.hℓ₀ (H.fd.good N 0 le_rfl (N - 1) (by omega)) (ctr d L N)
        (ctr d L N + prj x)
      rw [Complex.norm_real, Real.norm_eq_abs]
      refine this.trans (le_of_eq ?_)
      rw [ellj_sq, show N - 1 + 1 = N by omega]
    · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (rho_nonneg d L)
        (rho_lt_one hd3 hL2 (L := L))).const_mul (ℓ₀ ^ 2)
      rwa [mul_zero] at this
  have hsh : Tendsto (fun N : ℕ => ∑ k ∈ range (N - 1), (covZ stdPt d 0
      (Set.Ioc (lowEnd (L : ℝ) (k + 1)) ((L : ℝ) ^ (k + 1) / 2)) (-x) : ℂ)) atTop
      (𝓝 (greenZd d x : ℂ)) :=
    ht.comp (tendsto_sub_atTop_nat 1)
  have hsl := hsh.add hlast
  rw [add_zero] at hsl
  refine hsl.congr' ?_
  filter_upwards [eventually_ge_atTop (2 + supNormZ x)] with N hN
  have hs : supNormZ x ≤ L ^ (N - 1) := by
    have h1 : supNormZ x < L ^ supNormZ x := Nat.lt_pow_self (by omega)
    have h2 : L ^ supNormZ x ≤ L ^ (N - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h2s := two_s_lt hL3 hs (by omega)
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [sum_range_succ, show n + 1 - 1 = n by omega]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [covAt_pair_zero hd hL2 (by simp at hk; omega) h2s]

/-- **`Q1(x) = G_{ℤ^d}(x) + O(|b₀| |x|^{-(d-2+κ)})` at `m² = 0`**. -/
theorem Qone_zero_sub_green (hd3 : 3 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (b₀ : ℂ), ‖b₀‖ ≤ lbar →
    ∀ x : Zd d, x ≠ 0 →
      ‖Qone d L V₀c lbar 0 b₀ x - (greenZd d x : ℂ)‖ ≤
        K * ‖b₀‖ * (supNormZ x : ℝ) ^ (-((d : ℝ) - 2 + κ)) := by
  have hd2 : 2 ≤ d := by omega
  have hL3 := three_le_L H
  have hL2 : 2 ≤ L := by omega
  have hlb := H.fd.lbar_pos
  have hC0 := H.fd.C_nonneg
  have hκ := H.fd.κ_pos
  have hθ0 := th_nonneg L κ
  have hθ1 := th_lt_one hL2 hκ (L := L)
  have h1θ : 0 < 1 - th L κ := by linarith
  obtain ⟨Cr, Cb, hCr, hCb, hqs⟩ := qN_sub_le_one hd3
  obtain ⟨Cl, hCl, hla0⟩ := laOne_zero H hd hCs hS1 hd3
  -- the constant
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 4 * Cr * (C * lbar) + 2 * (Cl * lbar * (lbar + Cl * lbar * lbar) +
      lbar * (Cl * lbar)) + 4 * (Cb * (C * lbar) / (1 - th L κ)) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨M / lbar ^ 2 * (ℓ₀ ^ 2 * (L : ℝ) ^ ((d : ℝ) - 2 + κ)), by positivity, ?_⟩
  intro b₀ hb₀ x hx0
  -- the coalescence scale and the pair bound, uniform in `N`
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = Nat.log L (2 * supNormZ x) := ⟨_, rfl⟩
  have hlb2 : 0 < lbar ^ 2 := by positivity
  have hx1 : 1 ≤ supNormZ x := by
    by_contra h
    push_neg at h
    have h0 : supNormZ x = 0 := by omega
    apply hx0
    funext i
    have := natAbs_le_supNormZ x i
    rw [h0] at this
    simpa using Int.natAbs_eq_zero.1 (by omega)
  -- the error term
  have hpair : ∀ N : ℕ, 2 + supNormZ x ≤ N →
      ‖qN d L .one N 0 (V₀c 0 b₀) (initObs .one (lbar : ℂ)) (ctr d L N) (ctr d L N + prj x) -
          (lbar : ℂ) ^ 2 * ∑ k ∈ range N, (Flow.covAt d L N 0 k (ctr d L N)
            (ctr d L N + prj x) : ℂ)‖ ≤ M * ‖b₀‖ * (ellj d L ℓ₀ c ^ 2 * th L κ ^ c) ∧
      ellj d L ℓ₀ c ^ 2 * th L κ ^ c ≤
        ℓ₀ ^ 2 * ((L : ℝ) ^ ((d : ℝ) - 2 + κ) * (supNormZ x : ℝ) ^ (-((d : ℝ) - 2 + κ))) := by
    intro N hN
    have hs : supNormZ x ≤ L ^ (N - 1) := by
      have h1 : supNormZ x < L ^ supNormZ x := Nat.lt_pow_self (by omega)
      have h2 : L ^ supNormZ x ≤ L ^ (N - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have h2s := two_s_lt hL3 hs (by omega)
    have hb := ctr_add_prj_ne hL3 (N := N) (by omega) hx0 hs
    have hsn : supNorm (ctr d L N - (ctr d L N + prj x)) = supNormZ x := by
      rw [show ctr d L N - (ctr d L N + prj x) = -prj x by abel, supNorm_neg, supNorm_prj_of h2s]
    have hcoal : coal L (ctr d L N) (ctr d L N + prj x) = c := by
      rw [coal, hsn, hc]
    have hK : ∀ k < N, KnormObs .one ℓ₀ (ctr d L N) (ctr d L N + prj x) k A
        (flowO d L .one N 0 (V₀c 0 b₀) (initObs .one (lbar : ℂ)) (ctr d L N)
          (ctr d L N + prj x) k).2 ≤ ENNReal.ofReal (C * lbar * ‖b₀‖ * th L κ ^ k) := by
      intro k hk
      have := (H.fd.obs .one N 0 (lbar : ℂ) b₀ (ctr d L N + prj x) le_rfl
        (by rw [norm_lbar H]; exact hb₀) (le_of_eq (norm_lbar H)) hb k hk.le).2
      rwa [norm_lbar H, rpow_neg_mul_nat (Nat.cast_nonneg _) κ k] at this
    have hla : ∀ k ≤ N, ‖laOne d L N 0 (V₀c 0 b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x) k -
        lbar‖ ≤ Cl * lbar * ‖b₀‖ * th L κ ^ k := fun k hk => by
      have := (hla0 N b₀ _ hb₀ hb k hk).1
      rwa [rpow_neg_mul_nat (Nat.cast_nonneg _) κ k] at this
    have hlb' : ∀ k ≤ N, ‖lbOne d L N 0 (V₀c 0 b₀) (lbar : ℂ) (ctr d L N) (ctr d L N + prj x) k -
        lbar‖ ≤ Cl * lbar * ‖b₀‖ * th L κ ^ k := fun k hk => by
      have := (hla0 N b₀ _ hb₀ hb k hk).2
      rwa [rpow_neg_mul_nat (Nat.cast_nonneg _) κ k] at this
    have hE : 0 ≤ C * lbar * ‖b₀‖ := by positivity
    obtain ⟨hq, -⟩ := hqs L H.fd.hL8 N 0 (V₀c 0 b₀) ℓ₀ H.fd.hℓ₀ (H.fd.good N 0 le_rfl)
      (lbar : ℂ) (ctr d L N) (ctr d L N + prj x) A H.fd.hA1 hE hθ0 hθ1
      (by positivity : 0 ≤ Cl * lbar * ‖b₀‖) hK hla hlb'
    rw [hcoal, norm_lbar H] at hq
    refine ⟨hq.trans ?_, ?_⟩
    · have hX : 0 ≤ ellj d L ℓ₀ c ^ 2 * th L κ ^ c := by positivity
      refine mul_le_mul_of_nonneg_right ?_ hX
      rw [hM]
      have hbb : ‖b₀‖ * ‖b₀‖ ≤ lbar * ‖b₀‖ := mul_le_mul_of_nonneg_right hb₀ (norm_nonneg _)
      have e1 : Cl * lbar * ‖b₀‖ * (lbar + Cl * lbar * ‖b₀‖) ≤
          Cl * lbar * (lbar + Cl * lbar * lbar) * ‖b₀‖ := by
        have h1 : lbar + Cl * lbar * ‖b₀‖ ≤ lbar + Cl * lbar * lbar := by
          have := mul_le_mul_of_nonneg_left hb₀ (by positivity : 0 ≤ Cl * lbar); linarith
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ Cl * lbar * ‖b₀‖)
        linarith
      have e2 : 4 * (Cb * (C * lbar * ‖b₀‖) / (1 - th L κ)) =
          4 * (Cb * (C * lbar) / (1 - th L κ)) * ‖b₀‖ := by ring
      nlinarith [norm_nonneg b₀]
    · have := ellj_coal_sq_mul_pow_le hd2 hL2 ℓ₀ (s := κ) hκ.le (Ne.symm hb)
      rw [hcoal, hsn] at this
      exact this
  have hG := covsum_tendsto H hd hd3 x
  -- conclusion
  obtain ⟨-, hconv⟩ := hpair (2 + supNormZ x) le_rfl
  have hQ : Tendsto (fun N => qN d L .one N 0 (V₀c 0 b₀) (initObs .one (lbar : ℂ)) (ctr d L N)
      (ctr d L N + prj x) / (lbar : ℂ) ^ 2) atTop (𝓝 (Qone d L V₀c lbar 0 b₀ x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hρ1 := rho_lt_one hd3 hL2 (L := L)
    have ht := (tendsto_rpow_neg_mul (L := L) hL2 (s := (d : ℝ) - 2)
        (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd3); linarith)).const_mul
        (Kq lbar C κ Cs ℓ₀ b₀ L * (1 + 1 / (1 - rho d L)) / (rho d L * lbar ^ 2))
    rw [mul_zero] at ht
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ ht
    filter_upwards [eventually_ge_atTop (2 + supNormZ x)] with N hN
    have hs : supNormZ x ≤ L ^ (N - 1) := by
      have h1 : supNormZ x < L ^ supNormZ x := Nat.lt_pow_self (by omega)
      have h2 : L ^ supNormZ x ≤ L ^ (N - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    exact qN_rate H hd hCs hS1 hd3 le_rfl hb₀ hx0 (by omega) hs
  have hlim : Tendsto (fun N => qN d L .one N 0 (V₀c 0 b₀) (initObs .one (lbar : ℂ)) (ctr d L N)
      (ctr d L N + prj x) / (lbar : ℂ) ^ 2 - ∑ k ∈ range N, (Flow.covAt d L N 0 k (ctr d L N)
        (ctr d L N + prj x) : ℂ)) atTop
      (𝓝 (Qone d L V₀c lbar 0 b₀ x - (greenZd d x : ℂ))) := hQ.sub hG
  have hl2 : ((lbar : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hlb.ne')
  have hl2' : ‖((lbar : ℂ) ^ 2)‖ = lbar ^ 2 := by rw [norm_pow, norm_lbar H]
  refine le_of_tendsto hlim.norm ?_
  filter_upwards [eventually_ge_atTop (2 + supNormZ x)] with N hN
  obtain ⟨h1, -⟩ := hpair N hN
  have e : qN d L .one N 0 (V₀c 0 b₀) (initObs .one (lbar : ℂ)) (ctr d L N)
      (ctr d L N + prj x) / (lbar : ℂ) ^ 2 - ∑ k ∈ range N, (Flow.covAt d L N 0 k (ctr d L N)
        (ctr d L N + prj x) : ℂ) =
      (qN d L .one N 0 (V₀c 0 b₀) (initObs .one (lbar : ℂ)) (ctr d L N) (ctr d L N + prj x) -
        (lbar : ℂ) ^ 2 * ∑ k ∈ range N, (Flow.covAt d L N 0 k (ctr d L N)
          (ctr d L N + prj x) : ℂ)) / (lbar : ℂ) ^ 2 := by
    rw [sub_div, mul_div_cancel_left₀ _ hl2]
  rw [e, norm_div, hl2', div_le_iff₀ hlb2]
  refine h1.trans ?_
  have hb0 := norm_nonneg b₀
  have := mul_le_mul_of_nonneg_left hconv (by positivity : 0 ≤ M * ‖b₀‖)
  calc M * ‖b₀‖ * (ellj d L ℓ₀ c ^ 2 * th L κ ^ c)
      ≤ M * ‖b₀‖ * (ℓ₀ ^ 2 * ((L : ℝ) ^ ((d : ℝ) - 2 + κ) *
          (supNormZ x : ℝ) ^ (-((d : ℝ) - 2 + κ)))) := this
    _ = _ := by first | (field_simp; ring) | field_simp | ring

end

end Ward
