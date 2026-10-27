import Step2.Flow.FlowComplete2

/-!
# `thm:flow` with external requirements on `A` and `ε`, and the exported bulk data

`thm_flow_complete2X`: the conclusions of `thm_flow_complete2` (packaged as `FlowC2Concl`) for
constants with `A ∈ Aext L` and `ε ∈ Eext L A c_R c_x` (any requirements that hold on a half-line
in `A` and on an interval `(0, ε₀)` in `ε`), and the bulk data used along the observable flow:
`StepBounds` with constants uniform in `N`, and at every `N` and mass `ApHyp`, the mass
condition and the band (F1) (`BandF1`). With `Aext = Eext = True` this is `thm_flow_complete2`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L : ℕ} [NeZero L]

/-- The conclusion of `thm_flow_complete2` for given constants. -/
def FlowC2Concl (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke Cf Cb : ℝ) : Prop :=
  0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ Cf ∧ 0 ≤ Cb ∧ 2 * Cb * ε ≤ 1 / 4 ∧ ρ ≤ 1 / 8 ∧ SplitSmall Pc L ρ ∧
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
        |Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b - 1 / βR| ≤ 4 * Cb * (1 / βR) ^ 2) ∧
      -- strict monotonicity, uniqueness, continuity in `m²`
      (∀ m ∈ mRange L N, StrictMonoOn (gFinB R κ cm cT Nh ε m)
        (Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε)) ∧
      (∀ m ∈ mRange L N, ∀ βR : ℝ, 2 / ε ≤ βR →
        ∃! b, b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε ∧
          gFinB R κ cm cT Nh ε m b = 1 / βR) ∧
      (∀ βR : ℝ, 2 / ε ≤ βR →
        (∀ m ∈ mRange L N, bFin R κ cm cT Nh ε m (1 / βR) ∈
            Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε ∧
          gFinB R κ cm cT Nh ε m (bFin R κ cm cT Nh ε m (1 / βR)) = 1 / βR) ∧
        ContinuousOn (fun m => bFin R κ cm cT Nh ε m (1 / βR)) (mRange L N)) ∧
      -- validity of the parameters (exported for the zero-mode integration)
      (∀ m ∈ mRange L N, (∀ j < Nh, ValidAt (R.withMsq m) j) ∧ ValidAtL (R.withMsq m) Nh)

set_option maxHeartbeats 20000000 in
/-- **`thm_flow_complete2` with external requirements on `A` and `ε`**, and the exported bulk
data (`StepBounds`, and at every `N` and mass `ApHyp`, the mass condition, (F1)). -/
theorem thm_flow_complete2X (Aext : ℕ → ℝ → Prop) (hAext : ∀ L : ℕ, ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → Aext L A)
    (Eext : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hEext : ∀ (L : ℕ) (A c c' : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), Eext L A c c' ε) :
    ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb : ℝ, FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ Aext L A ∧
      ∃ C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx : ℝ,
        StepBounds L A C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx ∧
        (∀ R₀ : RGPar 2 L 1, R₀.ℓ = ℓ → Eext L A (cR R₀ ((L : ℝ) ^ 2) cm C₂x) (cx κ cT) ε) ∧
      ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
        R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
      ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
        ApHyp (R.withMsq m) ((L : ℝ) ^ 2) κ cg cm cT ε εsx C₀x C₂x Cqx Clx cSx ∧
        (∀ j < Nh, |(R.withMsq m).msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) ∧
        BandF1 (R.withMsq m) Nh κ cg cm cT ε := by
  obtain ⟨L₀, hL₀⟩ := flow_complete2_hyp0X Aext hAext Eext hEext
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, CNW, hAx, C₀x, ηx, εsx, CKx, C₂x, CDx,
    Cqx, Clx, cSx, hSBx, hEx, hCNW, hkf, hε1, hℓ, hA, hρ, hε,
    hκ0, hκ1, hcg, hcm, hcT, hKe, hCL, hCf, hCb, hCbε, hcgε, he, ha0, hs, hC, hρ8, hspl, hcov, h⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  obtain ⟨p, q, r, s, p₂, q₂, r₂, z₂, hCo, hp₂, hr₂, hz₂, hq₂⟩ := hC
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, ⟨hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe,
    hCf, hCb, hCbε, hρ8, hspl, fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh => ?_⟩, hAx, C₀x, ηx, εsx,
    CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx, fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm =>
      (h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh hNh.le).2.2.2⟩
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  have hL2n : 2 ≤ L := le_trans (le_max_right _ _) hL
  -- the bundles at every mass
  have hyp : ∀ m ∈ mRange L N, FinHypZ (R.withMsq m) Nh κ cg cm cT ε CL aB
      (eRange (betaL L) Ke 1) ∧
      (∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ∧
          BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ∧
      StrictMonoOn (gFinB R κ cm cT Nh ε m) (Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε) := by
    intro m hm
    obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, hglue, htop, -⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh hNh.le
    have hmass : m * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
      have := msq_horizon (L := (L : ℝ)) (by linarith) hm.2 (Nh := Nh) (k := 0) (by omega)
      simpa using this
    obtain ⟨hVL, TOP⟩ := htop hNh
    have hmono := gFin_strictMonoOn (R.withMsq m) hRℓ H HM hCo hp₂ hr₂ hz₂ hq₂ hV hVL TOP
      (fun b μ₀ hb => (hglue hNh b μ₀ hb).1) hCL hCf hCNW hε hε1 hL2n hkf
    refine ⟨⟨hV, H, HZ, HM, HD, e,
      { hc := hcg.le, he := he0
        hE := sum_e_le hL2 hm.1.le hKe H.hβ.le he0 hmass heb hej
        F1s := F1s }⟩, hglue hNh, ?_⟩
    refine hmono.mono fun b hb => ?_
    obtain ⟨μ, hμ, -⟩ := hb
    exact ⟨μ, hμ⟩
  obtain ⟨hFix, hMsq⟩ := flow_finalZ_of
    ⟨hρ, hρ8, hcov, hε, hcgε, he, ha0, hs, ⟨p, q, r, s, p₂, q₂, r₂, z₂, hCo⟩⟩ R hP hRρ
    (by omega) (by omega) le_rfl (fun m hm => (hyp m hm).1)
  have hcont := gFinB_contOn R (S := mRange L N) le_rfl (κ := κ) (cm := cm) (cT := cT) (ε := ε)
    (by omega) (by rw [hRρ]; exact hρ.le) (by rw [hRρ]; exact hρ8)
    (by rw [hP, hRρ]; exact hcov N (by omega)) (fun m hm => (hyp m hm).1.valid) hMsq
  obtain ⟨s1, s2⟩ := complete_shoot R hFix (fun m hm b μ₀ hb => ((hyp m hm).2.1 b μ₀ hb).2) hcont
    hε hCb hCbε
  have hmono : ∀ m ∈ mRange L N, StrictMonoOn (gFinB R κ cm cT Nh ε m)
      (Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε) := fun m hm => (hyp m hm).2.2
  refine ⟨hFix, hMsq, fun m hm => (hyp m hm).2.1, hcont, s1, s2, hmono, ?_, ?_, ?_⟩
  · intro m hm βR hβR
    obtain ⟨b, hb, hby⟩ := s1 m hm βR hβR
    refine ⟨b, ⟨hb, hby⟩, fun b' hb' => ?_⟩
    rcases lt_trichotomy b' b with hlt | heq | hgt
    · have := hmono m hm hb'.1 hb hlt; rw [hb'.2, hby] at this; exact absurd this (lt_irrefl _)
    · exact heq
    · have := hmono m hm hb hb'.1 hgt; rw [hb'.2, hby] at this; exact absurd this (lt_irrefl _)
  · intro βR hβR
    have hspec : ∀ m ∈ mRange L N, bFin R κ cm cT Nh ε m (1 / βR) ∈
        Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε ∧
        gFinB R κ cm cT Nh ε m (bFin R κ cm cT Nh ε m (1 / βR)) = 1 / βR :=
      fun m hm => bFin_spec R (s1 m hm βR hβR)
    refine ⟨hspec, contOn_shoot (U := fun m => Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε)
      (f := gFinB R κ cm cT Nh ε) hMsq.isOpen hcont hmono hspec⟩
  · intro m hm
    exact ⟨(hyp m hm).1.valid, ((h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh
      hNh.le).2.2.1 hNh).1⟩

end

end Step2
