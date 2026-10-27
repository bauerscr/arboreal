import Step2.Flow.FlowCompleteHyp
import Step2.Last.FlowLastCont
import Step2.Flow.FlowFinalZ
import Flow2.Complete

/-!
# Expected result `thm:flow` with the last two steps and the shooting on `ǧ_N`

`thm_flow_complete`: one set of constants `ℓ, A, ρ, κ, c_g, c_m, c_T, ε, K_e, C_f, C_b`
(independent of `N`, `m²`) such that for every `N ≥ 2`, `R` (`P = Pc`, `i₀ = 0`) and the horizon
`N_h = N - 2`:

* (`thm_flow_final`) for every `0 < m² ≤ L^{-2(N-1)}` the flow up to `N_h` satisfies `FixedConcl`
  and the mass dependence `MsqConcl`;
* (`thm_flow_last`) along every admissible trajectory the last two steps satisfy `GlueOut`;
* (weak band) `BandOut`: `|ǧ_{N-1} - ǧ_{N-2}| ≤ C_b ǧ_{N-2}²` and
  `|ǧ_N - Re ǧ_{N-1}| ≤ C_b ǧ_{N-2}²`, hence `|Re ǧ_N - ǧ_{N-2}| ≤ 2 C_b ǧ_{N-2}²`;
  here `ǧ_N = κ_N.g/Z_N²` (`lastG`), the final quartic coupling of `V_N = V_{κ_N}`;
* (continuity) `(m², b) ↦ Re ǧ_N` is continuous on the relatively open `UfixM`;
* (shooting on `ǧ_N`, existence) for every `m²` and every `β_R ≥ 2/ε` there is `b ∈ Ufix` with
  `Re ǧ_N(b) = 1/β_R`; every such `b` has `|ǧ_{N-2}(b) - 1/β_R| ≤ 4 C_b β_R^{-2}`.

Uniqueness of `b` in the shooting on `ǧ_N` (strict monotonicity of `b ↦ ǧ_N`) is **not** proved:
it needs the Lipschitz layer (`FlowLip*`, `FlowZeta*`) at the step `j = N - 2` (under `ValidAtL`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L : ℕ} [NeZero L]

/-- `ǧ_N(b)` along the admissible flow at mass `m²`. -/
def gFinB {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (κ cm cT : ℝ) (Nh : ℕ)
    (ε m b : ℝ) : ℝ :=
  gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b))

/-- **The shooting on `ǧ_N`** from the conclusions at one mass: existence for `y ≤ ε/2`, and the
localisation of every solution. -/
theorem shoot_gFin {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {β κ cg cm cT ε E Cb : ℝ} {Nh : ℕ} {m : ℝ}
    (hF : FixedConcl (rgDataM R m) ((L : ℝ) ^ 2) β κ cg cm cT Nh ε E)
    (hB : ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
      BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (hc : ContinuousOn (gFinB R κ cm cT Nh ε m) (Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε))
    (hCb : 0 ≤ Cb) (hCε : 2 * Cb * ε ≤ 1 / 4) :
    (∀ y, 0 < y → y ≤ ε / 2 → ∃ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε,
      gFinB R κ cm cT Nh ε m b = y) ∧
    (∀ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε, ∀ y, gFinB R κ cm cT Nh ε m b = y →
      |Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b - y| ≤ 4 * Cb * y ^ 2) := by
  set F := rgDataM R m
  set U := Ufix F ((L : ℝ) ^ 2) κ cm cT Nh ε
  have hspec : ∀ b ∈ U, Admissible F ((L : ℝ) ^ 2) κ cm cT Nh ε b
      (Hist.muc F ((L : ℝ) ^ 2) κ cm cT Nh ε b) := fun b hb => by
    obtain ⟨μ, hμ, -⟩ := hb
    have hex : ∃ μ, Admissible F ((L : ℝ) ^ 2) κ cm cT Nh ε b μ := ⟨μ, hμ⟩
    unfold Hist.muc; rw [dif_pos hex]; exact hex.choose_spec
  have hfg : ∀ b ∈ U, |gFinB R κ cm cT Nh ε m b - Hist.gN F ((L : ℝ) ^ 2) κ cm cT Nh ε b| ≤
      (2 * Cb) * Hist.gN F ((L : ℝ) ^ 2) κ cm cT Nh ε b ^ 2 := fun b hb => by
    have h := (hB b _ (hspec b hb)).gFin_sub
    unfold gFinB Hist.gN
    exact h
  have hmono : StrictMonoOn (Hist.gN F ((L : ℝ) ^ 2) κ cm cT Nh ε) U :=
    hF.strictMono.mono fun b hb => ⟨_, hspec b hb⟩
  have hgpos : ∀ b ∈ U, 0 < Hist.gN F ((L : ℝ) ^ 2) κ cm cT Nh ε b ∧
      Hist.gN F ((L : ℝ) ^ 2) κ cm cT Nh ε b < ε := fun b hb => by
    have : Hist.gN F ((L : ℝ) ^ 2) κ cm cT Nh ε b ∈ Ioo 0 ε := by
      rw [← hF.image]; exact mem_image_of_mem _ hb
    exact this
  refine ⟨exists_eq_of_perturb hF.ordConnected hmono hF.image hc hfg (by positivity) hCε,
    fun b hb y hy => ?_⟩
  obtain ⟨h0, hε⟩ := hgpos b hb
  have hC : 0 ≤ 2 * Cb := by positivity
  have hCg : 2 * Cb * Hist.gN F ((L : ℝ) ^ 2) κ cm cT Nh ε b ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left hε.le hC).trans hCε
  have h := hfg b hb
  rw [hy] at h
  have := g_near_of_eq hC h0.le hCg h
  linarith only [this, show 2 * (2 * Cb) * y ^ 2 = 4 * Cb * y ^ 2 by ring]

/-- `gFin_contOn_UfixM` in terms of `gFinB`. -/
theorem gFinB_contOn {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {S : Set ℝ}
    (hS : S ⊆ mRange L N) {κ cm cT ε : ℝ} {Nh : ℕ} (hNh : Nh < N) (hρ : 0 ≤ R.ρ)
    (hρ8 : R.ρ ≤ 1 / 8) (hcov : CovContM R.P L N 2 R.ρ)
    (hV : ∀ m ∈ S, ∀ j < Nh, ValidAt (R.withMsq m) j) (hM : MsqConcl R κ cm cT Nh ε S) :
    ContinuousOn (fun q : ℝ × ℝ => gFinB R κ cm cT Nh ε q.1 q.2) (UfixM R κ cm cT Nh ε S) := by
  unfold gFinB
  exact gFin_contOn_UfixM R hS hNh hρ hρ8 hcov hV hM

attribute [local irreducible] gFinB in
/-- **The shooting on `ǧ_N` on a set of masses** (from `shoot_gFin`). -/
theorem complete_shoot {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {β κ cg cm cT ε E Cb : ℝ} {Nh : ℕ} {S : Set ℝ}
    (hF : ∀ m ∈ S, FixedConcl (rgDataM R m) ((L : ℝ) ^ 2) β κ cg cm cT Nh ε E)
    (hB : ∀ m ∈ S, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
      BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (hc : ContinuousOn (fun q : ℝ × ℝ => gFinB R κ cm cT Nh ε q.1 q.2) (UfixM R κ cm cT Nh ε S))
    (hε : 0 < ε) (hCb : 0 ≤ Cb) (hCε : 2 * Cb * ε ≤ 1 / 4) :
    (∀ m ∈ S, ∀ βR : ℝ, 2 / ε ≤ βR →
      ∃ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε, gFinB R κ cm cT Nh ε m b = 1 / βR) ∧
    (∀ m ∈ S, ∀ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε, ∀ βR : ℝ,
      gFinB R κ cm cT Nh ε m b = 1 / βR →
      |Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b - 1 / βR| ≤ 4 * Cb * (1 / βR) ^ 2) := by
  have hc1 : ∀ m ∈ S, ContinuousOn (gFinB R κ cm cT Nh ε m)
      (Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε) := fun m hm =>
    hc.comp (f := fun b : ℝ => (m, b)) (continuousOn_const.prodMk continuousOn_id)
      fun b hb => (⟨hm, hb⟩ : m ∈ S ∧ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε)
  refine ⟨fun m hm βR hβR => ?_, fun m hm b hb βR hy =>
    (shoot_gFin R (hF m hm) (hB m hm) (hc1 m hm) hCb hCε).2 b hb _ hy⟩
  have hβ0 : 0 < βR := lt_of_lt_of_le (by positivity) hβR
  refine (shoot_gFin R (hF m hm) (hB m hm) (hc1 m hm) hCb hCε).1 (1 / βR) (by positivity) ?_
  rw [div_le_iff₀ hε] at hβR
  rw [div_le_div_iff₀ hβ0 (by norm_num)]
  linarith

set_option maxHeartbeats 20000000 in
/-- **Expected result `thm:flow` with the last two steps, and the shooting on `ǧ_N`.**
One set of constants; for every `N ≥ 2`, `R`, `N_h = N - 2`: the conclusions of `thm_flow_final`
(`FixedConcl` for every mass, `MsqConcl`), the bounds `GlueOut` of `thm_flow_last` and the weak
band `BandOut` of the last two steps along every admissible trajectory, the joint continuity of
`(m², b) ↦ Re ǧ_N` on `UfixM`, and the shooting on `Re ǧ_N` (existence for `β_R ≥ 2/ε`, with
`|ǧ_{N-2}(b) - 1/β_R| ≤ 4 C_b/β_R²` for every solution). -/
theorem thm_flow_complete : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ Cf ∧ 0 ≤ Cb ∧ 2 * Cb * ε ≤ 1 / 4 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N →
      (∀ m ∈ mRange L N, FixedConcl (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
          (eRange (betaL L) Ke 1)) ∧
      MsqConcl R κ cm cT Nh ε (mRange L N) ∧
      (∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ∧
          BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ∧
      ContinuousOn (fun q : ℝ × ℝ => gFinB R κ cm cT Nh ε q.1 q.2)
        (UfixM R κ cm cT Nh ε (mRange L N)) ∧
      (∀ m ∈ mRange L N, ∀ βR : ℝ, 2 / ε ≤ βR →
        ∃ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε, gFinB R κ cm cT Nh ε m b = 1 / βR) ∧
      (∀ m ∈ mRange L N, ∀ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε, ∀ βR : ℝ,
        gFinB R κ cm cT Nh ε m b = 1 / βR →
        |Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b - 1 / βR| ≤ 4 * Cb * (1 / βR) ^ 2) := by
  obtain ⟨L₀, hL₀⟩ := flow_complete_hyp0
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT,
    hKe, hCL, hCf, hCb, hCbε, hcgε, he, ha0, hs, hC, hρ8, hcov, h⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe,
    hCf, hCb, hCbε, fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh => ?_⟩
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  -- the bundles at every mass
  have hyp : ∀ m ∈ mRange L N, FinHypZ (R.withMsq m) Nh κ cg cm cT ε CL aB
      (eRange (betaL L) Ke 1) ∧
      (∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ∧
          BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) := by
    intro m hm
    obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, hglue⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh hNh.le
    have hmass : m * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
      have := msq_horizon (L := (L : ℝ)) (by linarith) hm.2 (Nh := Nh) (k := 0) (by omega)
      simpa using this
    exact ⟨⟨hV, H, HZ, HM, HD, e,
      { hc := hcg.le, he := he0
        hE := sum_e_le hL2 hm.1.le hKe H.hβ.le he0 hmass heb hej
        F1s := F1s }⟩, hglue hNh⟩
  obtain ⟨hFix, hMsq⟩ := flow_finalZ_of ⟨hρ, hρ8, hcov, hε, hcgε, he, ha0, hs, hC⟩ R hP hRρ
    (by omega) (by omega) le_rfl (fun m hm => (hyp m hm).1)
  have hcont := gFinB_contOn R (S := mRange L N) le_rfl (κ := κ) (cm := cm) (cT := cT) (ε := ε)
    (by omega) (by rw [hRρ]; exact hρ.le) (by rw [hRρ]; exact hρ8)
    (by rw [hP, hRρ]; exact hcov N (by omega)) (fun m hm => (hyp m hm).1.valid) hMsq
  obtain ⟨s1, s2⟩ := complete_shoot R hFix (fun m hm b μ₀ hb => ((hyp m hm).2 b μ₀ hb).2) hcont hε
    hCb hCbε
  exact ⟨hFix, hMsq, fun m hm => (hyp m hm).2, hcont, s1, s2⟩

end

end Step2
