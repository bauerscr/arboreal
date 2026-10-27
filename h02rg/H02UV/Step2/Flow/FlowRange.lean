import Step2.Flow.FlowRangeHyp
import Flow2.RangeFlow

/-!
# The flow theorem on the sharp range (`h02uv-outline.tex`, Expected result `thm:flow`)

`thm_flow_range`: `thm_flow_sharp` with the range `b ∈ (0, b_max]`, `1/b_max = 1/ε + N_h β₊`,
replaced by the sharp range `b ∈ (0, b_maxS]`,

  `1/b_maxS = 1/ε + β N_h + E + (c_g/β) log(1 + β N_h ε)`,  `E = β/2 + K_e (1 + 2ϑ)`

(`Flow2.Hist.bmaxS`), obtained from the summable sharp (F1) (`flow_range_hyp`) and the abstract
sharp range (`Flow2.Hist.fh_flow_range`, `Flow2.Hist.ginv_log`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2.D2

/-- The summed error of the sharp (F1): `E = β/2 + K_e (1 + 2ϑ)`. -/
def eRange (β Ke ϑ : ℝ) : ℝ := 1 / 2 * β + Ke * (1 + 2 * ϑ)

/-- `∑_{j<N_h} e_j ≤ β/2 + K_e (1 + 2ϑ)` if `e_0 ≤ β/2` and
`e_j ≤ K_e (L^{-2j} + m² L^{2(j+1)})` for `j ≥ 1`. -/
theorem sum_e_le {e : ℕ → ℝ} {β Ke L msq ϑ : ℝ} {Nh : ℕ} (hL : 2 ≤ L) (hmsq : 0 ≤ msq)
    (hKe : 0 ≤ Ke) (hβ : 0 ≤ β) (he : ∀ j, 0 ≤ e j) (hϑ : msq * (L ^ (Nh + 1)) ^ 2 ≤ ϑ)
    (h0 : ∀ j < Nh, e j ≤ 1 / 2 * β)
    (h1 : ∀ j, 1 ≤ j → e j ≤ Ke * (((L ^ j) ^ 2)⁻¹ + msq * (L ^ (j + 1)) ^ 2)) :
    ∑ j ∈ range Nh, e j ≤ eRange β Ke ϑ := by
  have hϑ0 : 0 ≤ ϑ := le_trans (by positivity) hϑ
  unfold eRange
  rcases Nat.eq_zero_or_pos Nh with rfl | hN
  · simp only [range_zero, sum_empty]; positivity
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hN]
  have hs : ∑ j ∈ Ico 1 Nh, e j ≤ Ke * (1 + 2 * ϑ) := by
    refine (sum_le_sum fun j hj => h1 j (mem_Ico.1 hj).1).trans ?_
    rw [← mul_sum, sum_add_distrib, ← mul_sum]
    have hI := geom_inv_le hL Nh
    have hsub : Ico 1 Nh ⊆ range Nh := by
      rw [range_eq_Ico]; exact Ico_subset_Ico (Nat.zero_le 1) le_rfl
    have hM1 : ∑ j ∈ Ico 1 Nh, (L ^ (j + 1)) ^ 2 ≤ ∑ j ∈ range Nh, (L ^ (j + 1)) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => sq_nonneg _
    have hM2 := geom_Lsq_le hL Nh
    have hM3 : (L ^ Nh) ^ 2 ≤ (L ^ (Nh + 1)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega)) 2
    have hM : msq * ∑ j ∈ Ico 1 Nh, (L ^ (j + 1)) ^ 2 ≤ 2 * ϑ := by
      have := mul_le_mul_of_nonneg_left (hM1.trans (hM2.trans (mul_le_mul_of_nonneg_left hM3
        (by norm_num)))) hmsq
      linarith only [this, hϑ]
    exact mul_le_mul_of_nonneg_left (by linarith only [hI, hM]) hKe
  have := h0 0 hN
  linarith only [hs, this]

set_option maxHeartbeats 4000000 in
/-- **Expected result `thm:flow` on the sharp range.** For `L ≥ L₀` there are constants such
that for all `N`, `0 < m² ≤ L^{-2(N-1)}` and horizons `N_h + 2 ≤ N` with `m² L^{2(N_h+1)} ≤ ϑ`,
with `β = 3 log L/(2π)`, `E = β/2 + K_e (1 + 2ϑ)` and
`1/b_maxS = 1/ε + β N_h + E + (c_g/β) log(1 + β N_h ε)`:
* for `b ∈ (0, b_maxS]` there is a unique admissible `μ₀`, and `μ₀(b)`, `ǧ_{N_h}(b)` are
  continuous on `(0, b_maxS]`;
* along the admissible flow from `b ∈ (0, b_maxS]`, `1/ǧ_j ≥ 1/ε + β (N_h - j)`;
* `1/ǧ_{N_h}(b_maxS) ≤ ginvS = 1/ε + (3 + 2β) E + ((c_g + C)/β) log(1 + β N_h ε)`, and every
  final coupling `ǧ_{N_h}(b) = 1/β_R` with `β_R ≥ ginvS` is attained by some `b ∈ (0, b_maxS]`;
* (i), logarithmic form: along every admissible trajectory and for `n ≤ N_h`,
  `|1/ǧ_n - 1/b + β n| ≤ 2(1+β) E + (5C/β) log(ǧ_n/b)`, `C = 2(β² + (1+β) c_g)`. -/
theorem thm_flow_range : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ ϑ κ cg cm cT ε Ke : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ϑ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ Nh : ℕ, Nh + 2 ≤ N → R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ ϑ →
      1 / bmaxS (betaL L) cg (eRange (betaL L) Ke ϑ) Nh ε =
          1 / ε + betaL L * Nh + eRange (betaL L) Ke ϑ +
            cg / betaL L * Real.log (1 + betaL L * Nh * ε) ∧
      (∀ b ∈ Set.Ioc 0 (bmaxS (betaL L) cg (eRange (betaL L) Ke ϑ) Nh ε),
          ∃! μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀) ∧
      ContinuousOn (muc (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε)
        (Set.Ioc 0 (bmaxS (betaL L) cg (eRange (betaL L) Ke ϑ) Nh ε)) ∧
      ContinuousOn (gN (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε)
        (Set.Ioc 0 (bmaxS (betaL L) cg (eRange (betaL L) Ke ϑ) Nh ε)) ∧
      (∀ b ∈ Set.Ioc 0 (bmaxS (betaL L) cg (eRange (betaL L) Ke ϑ) Nh ε), ∀ μ₀,
        Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → ∀ j ≤ Nh,
          1 / ε + betaL L * ((Nh : ℝ) - j) ≤ 1 / (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j).1) ∧
      1 / gN (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε
          (bmaxS (betaL L) cg (eRange (betaL L) Ke ϑ) Nh ε) ≤
        ginvS (betaL L) cg (eRange (betaL L) Ke ϑ) Nh ε ∧
      (∀ βR, ginvS (betaL L) cg (eRange (betaL L) Ke ϑ) Nh ε ≤ βR →
        ∃ b ∈ Set.Ioc 0 (bmaxS (betaL L) cg (eRange (betaL L) Ke ϑ) Nh ε),
          gN (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b = 1 / βR) ∧
      (∀ b μ₀, Admissible (rgData R) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → ∀ n ≤ Nh,
        |1 / (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ n).1 - 1 / b + betaL L * n| ≤
          2 * (1 + betaL L) * eRange (betaL L) Ke ϑ +
            5 * Cgu (betaL L) cg / betaL L *
              Real.log ((traj (rgData R) ((L : ℝ) ^ 2) b μ₀ n).1 / b)) := by
  obtain ⟨L₀, hL₀⟩ := flow_range_hyp
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, ϑ, κ, cg, cm, cT, ε, Ke, hℓ, hA, hρ, hϑ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe,
    hcgε, h⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  refine ⟨ℓ, A, ρ, ϑ, κ, cg, cm, cT, ε, Ke, hℓ, hA, hρ, hϑ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh hmass => ?_⟩
  obtain ⟨Ah, ah, e, H, he, ha0, he0, F1s, heb, hej⟩ :=
    h N R hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh hmass
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  have hβ : 0 < betaL L := H.hβ
  have S : SharpHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh ε cg
      (eRange (betaL L) Ke ϑ) e :=
    { hc := hcg.le, he := he0
      hE := sum_e_le hL2 hm0.le hKe hβ.le he0 hmass heb hej
      F1s := F1s }
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := fh_flow_range H he S hε ha0
  have hgβ : cg * ε ≤ (1 - 1 / 2) * betaL L / 2 := by linarith only [hcgε]
  refine ⟨by unfold bmaxS; rw [one_div_one_div], r1, r2, r3, r4, r5, r6,
    fun b μ₀ hadm n hn => ginv_log H he hgβ S hadm hn⟩

end

end Step2
