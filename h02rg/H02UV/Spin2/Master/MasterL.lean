import Spin2.Gam.GamTop
import Step2.Flow.FlowMasterHypL

/-!
# The master construction with the validity of the last step exported

* `LastValidConcl`: `LastN.ValidLast (R.withMsq m) (N_h + 1)` for every admissible parameter set
  (the last-step covariance `stCovN` then satisfies `GoodCov2`, `LastN.covN`).
* **`thm_flow_masterL`**: `thm_flow_master` (same proof, via `Step2.flow_master_hyp0L`) and in
  addition `LastValidConcl`.
* **`thm_gamTop_master`**: `FlowC2Concl`, `ε ≤ 1`, `SpinConcl`, `MagConcl`, `GMonoConcl` and
  `LastValidConcl` with one set of constants.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

set_option maxHeartbeats 20000000 in
/-- **The master flow theorem.** One construction of the constants for: `thm_flow_complete2X`
(`FlowC2Concl`: `thm:flow` with the last two steps and the shooting `Re ǧ_N = 1/β_R`; the external
requirements `A ∈ Aext L`, `ε ∈ Eext …`; the exported bulk data) and `SpinConcl` (the
conclusions of `thm_flow_final_spinX` and the per-step band of `β_j`). -/
theorem thm_flow_masterL (Aext : ℕ → ℝ → Prop) (hAext : ∀ L : ℕ, ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → Aext L A)
    (Eext : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hEext : ∀ (L : ℕ) (A c c' : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), Eext L A c c' ε) :
    ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ, FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧
      ε ≤ 1 ∧ 0 ≤ KZ ∧ 0 ≤ KG ∧ SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧ Aext L A ∧
      ValidConcl L ℓ A ρ κ cg cm cT ε ∧ LastValidConcl L ℓ ρ ∧
      ∃ C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx : ℝ,
        StepBounds L A C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx ∧
        (∀ R₀ : RGPar 2 L 1, R₀.ℓ = ℓ → Eext L A (cR R₀ ((L : ℝ) ^ 2) cm C₂x) (cx κ cT) ε) ∧
      ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
        R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
      ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
        ApHyp (R.withMsq m) ((L : ℝ) ^ 2) κ cg cm cT ε εsx C₀x C₂x Cqx Clx cSx ∧
        (∀ j < Nh, |(R.withMsq m).msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) ∧
        BandF1 (R.withMsq m) Nh κ cg cm cT ε := by
  obtain ⟨L₀, hL₀⟩ := flow_master_hyp0L Aext hAext Eext hEext
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, CNW, AZ, cz, KG, Kz, hAx, hAZ, hcz, hKG,
    hKz, C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx, hCNW, hkf, hε1, hℓ, hA, hρ, hε,
    hκ0, hκ1, hcg, hcm, hcT, hKe, hCL, hCf, hCb, hCbε, hcgε, he, ha0, hs, hC, hρ8, hspl, hcov, hVLast, h⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  obtain ⟨p, q, r, s, p₂, q₂, r₂, z₂, hCo, hp₂, hr₂, hz₂, hq₂⟩ := hC
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  have hL2n : 2 ≤ L := le_trans (le_max_right _ _) hL
  have hβ : 0 < betaL L := by
    unfold betaL
    have : 0 < Real.log L := Real.log_pos (by linarith only [hL2])
    have := Real.pi_pos
    positivity
  have heR : 0 ≤ eRange (betaL L) Ke 1 := by unfold eRange; positivity
  obtain ⟨KZ, hKZd⟩ : ∃ KZ : ℝ, KZ = logTrajK (betaL L) cg AZ (1 / 3) + AZ * 4 +
      1 / 3 * (2 * (1 + betaL L) * eRange (betaL L) Ke 1) := ⟨_, rfl⟩
  have hK0 : 0 ≤ logTrajK (betaL L) cg AZ (1 / 3) := by
    unfold logTrajK Cgu; positivity
  have hKZ : 0 ≤ KZ := by rw [hKZd]; positivity
  have hc : FinConstZ L ρ κ cg cm cT ε CL aB := ⟨hρ, hρ8, hcov, hε, hcgε, he, ha0, hs,
    ⟨p, q, r, s, p₂, q₂, r₂, z₂, hCo⟩⟩
  -- the conclusions of `thm_flow_complete2X`
  have hC2 : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb := by
    refine ⟨hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe, hCf, hCb, hCbε, hρ8, hspl,
      fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh => ?_⟩
    have hyp : ∀ m ∈ mRange L N, FinHypZ (R.withMsq m) Nh κ cg cm cT ε CL aB
        (eRange (betaL L) Ke 1) ∧
        (∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
          GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ∧
            BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ∧
        StrictMonoOn (gFinB R κ cm cT Nh ε m) (Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε) := by
      intro m hm
      obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, hglue, htop, -, -⟩ :=
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
    obtain ⟨hFix, hMsq⟩ := flow_finalZ_of hc R hP hRρ (by omega) (by omega) le_rfl
      (fun m hm => (hyp m hm).1)
    have hcont := gFinB_contOn R (S := mRange L N) le_rfl (κ := κ) (cm := cm) (cT := cT) (ε := ε)
      (by omega) (by rw [hRρ]; exact hρ.le) (by rw [hRρ]; exact hρ8)
      (by rw [hP, hRρ]; exact hcov N (by omega)) (fun m hm => (hyp m hm).1.valid) hMsq
    obtain ⟨s1, s2⟩ := complete_shoot R hFix (fun m hm b μ₀ hb => ((hyp m hm).2.1 b μ₀ hb).2)
      hcont hε hCb hCbε
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
  -- the conclusions of `thm_flow_final_spinX`
  have hSp : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ (gamKX L cz KG Kz) := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh
    have hmass : ∀ m ∈ mRange L N, m * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := fun m hm => by
      have := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
        (by omega)
      simpa using this
    have hyp : ∀ m ∈ mRange L N, FinHypZ (R.withMsq m) Nh κ cg cm cT ε CL aB
        (eRange (betaL L) Ke 1) := fun m hm => by
      obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      exact ⟨hV, H, HZ, HM, HD, e,
        { hc := hcg.le, he := he0
          hE := sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej
          F1s := F1s }⟩
    obtain ⟨c1, c2⟩ := flow_finalZ_of hc R hP hRρ hN (by omega) le_rfl hyp
    have hLS : ∀ m ∈ mRange L N, LogSum (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
        (eRange (betaL L) Ke 1) := fun m hm => by
      obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      exact logSum_of H he hε1 hcgε he0 heb
        (sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej) F1s
    have hSS : ∀ m ∈ mRange L N, SpinSum (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
        (eRange (betaL L) Ke 1) := fun m hm => by
      obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      exact spinSum_of H he hε1 hcgε he0 heb
        (sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej) F1s
    have hBA : ∀ m ∈ mRange L N, BetaAsym (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
        (eRange (betaL L) Ke 1) := fun m hm => by
      obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      exact betaAsym_of H he hε1 hcgε he0 heb
        (sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej) F1s
    refine ⟨c1, c2, hLS, hSS, hBA, fun m hm b μ₀ hadm k hk => ?_, fun m hm b μ₀ hadm n hn => ?_,
      fun m hm b μ₀ hadm k hk => ?_⟩
    · -- the per-step band
      obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      obtain ⟨-, -, -, -, hband, -⟩ := traj_facts H he hε1 hcgε he0 heb F1s hadm
      have h1 := e_le_zA (β := betaL L) (Ke := Ke) (L := L) (m := m) heb hej hm.1.le hk
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (1 + betaL L))
      have h3 : 2 * (1 + betaL L) * e k ≤ 2 * (1 + betaL L) * max Ke (betaL L / 2) * zA L m k :=
        h2.trans_eq (by ring)
      exact (hband k hk).trans (add_le_add h3 le_rfl)
    · obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -, -, -, hZs, -⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
      have hD := admissible_InDh H hadm
      have hρ0' : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = ρ from hRρ]; exact hρ.le
      have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = ρ from hRρ]; exact hρ8
      refine ⟨Z_succ_ne_zero (R.withMsq m) hρ0' hρ8' (fun i hi => hV i (by omega)) t, ?_⟩
      have key := hLS m hm b μ₀ hadm
        (fun k => Real.log ‖(rawHist (R.withMsq m) (k + 1) t).Z‖) (fun _ => 0) (zA L m) AZ
        (betaL L / 3) hAZ (zA_nonneg L hm.1.le)
        (fun k hk => by
          have := hZs k hk t (hD (k + 1) (by omega))
          simp only [sub_self, sub_zero]
          exact this) n hn
      have hy0 : Real.log ‖(rawHist (R.withMsq m) 1 t).Z‖ = 0 := by
        rw [rawHist_one_Z, norm_one, Real.log_one]
      have hy0' : Real.log ‖(rawHist (R.withMsq m) (0 + 1) t).Z‖ = 0 := hy0
      simp only [hy0, sub_self, sub_zero] at key
      have hβne : betaL L ≠ 0 := hβ.ne'
      have hs3 : |betaL L / 3| / betaL L = 1 / 3 := by
        rw [abs_of_pos (by positivity)]; field_simp
      have hs3' : betaL L / 3 / betaL L = 1 / 3 := by field_simp
      rw [hs3, hs3'] at key
      refine key.trans (mul_le_mul_of_nonneg_right ?_ ((hD n hn).1 n le_rfl).1.le)
      rw [hKZd]
      have hsa := sum_zA_le (Ln := L) rfl hL2 hm.1.le n
      have hmn : m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := by
        refine le_trans ?_ (hmass m hm)
        refine mul_le_mul_of_nonneg_left ?_ hm.1.le
        exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2])
          (by omega)) 2
      have := Real.pi_pos
      linarith only [hsa, hmn, mul_le_mul_of_nonneg_left (by linarith only [hsa, hmn] :
        ∑ k ∈ range n, zA L m k ≤ 4) hAZ]
    · obtain ⟨⟨e, hV, -, H, -⟩, -, -, -, -, hMzb, hcov0, hval⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      have hD := admissible_InDh H hadm
      have hρ0' : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = ρ from hRρ]; exact hρ.le
      have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = ρ from hRρ]; exact hρ8
      exact ⟨gam_hist_bound (R.withMsq m) hP hNh hcz hKG hKz hL2 hm.1.le _ hV
        (fun j hj => hMzb j hj _ (hD j hj.le)) (fun j hj => hcov0 j hj _ (hD j hj.le)) hval
        (fun j hj => ((hD j hj.le).1 j le_rfl).1.le) k hk,
        Z_eq_norm_hist (R.withMsq m) hρ0' hρ8' _ _ _ (k + 1)⟩
  have hVC : ValidConcl L ℓ A ρ κ cg cm cT ε := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
    exact ⟨hV, fun b μ₀ hadm k hk => (traj_facts H he hε1 hcgε he0 heb F1s hadm).2.2.2.1 k hk⟩
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, gamKX L cz KG Kz, hC2, hε1, hKZ,
    gamKX_nonneg hL2 hcz hKG hKz, hSp, hAx, hVC,
    (fun N R hP hRℓ hRρ hN Nh hNh m hm =>
      hVLast N (R.withMsq m) hP hRℓ hRρ (by omega) hm.1 hm.2 Nh hNh), C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm =>
      (h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh hNh.le).2.2.2.1⟩

end

end Spin2
