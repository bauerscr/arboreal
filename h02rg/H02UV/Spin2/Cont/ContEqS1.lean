import Spin2.Final.FinalAllX
import Spin2.Cont.ContEq1

set_option autoImplicit false

/-!
# B3, `r`-dependent form: per-`M` copies of the final chain (I)

`fb_consts6`, `fb_constsT`, `ct_main` and `thm_multiscale_final_h0_allB` obtain their master
construction from `thm_master_all`; their bodies are generic in `M`. Here they are restated for a
**given** `M : MasterFacts L` (verbatim copies of the bodies), so that they can be run on the
construction of `thm_master_all_cab` (`0 < c_{ab}`):
`eqs_consts6`, `eqs_constsT`, `eqs_ctMain`, `eqs_allB`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 4000000 in
/-- `fb_consts6` for a given `M`. -/
theorem eqs_consts6 (M : MasterFacts L) :
    ∃ (pW g₀ K : ℝ), 0 < g₀ ∧ g₀ ≤ M.core.ε / 2 ∧
      pW * cmu ((L : ℝ) ^ 2) M.core.cm ≤ 1 / 12 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 3 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, M.Kp * zA L m (Nh - 1) ≤ 1 / 2 →
    ∀ b μc : ℝ, 0 < b →
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μc →
      m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ≤ g₀ → FwRes6 M pW K R Nh m b μc := by
  obtain ⟨pW, r₀, hs, hr₀, -, hE⟩ := M.fb_h0EndsGS
  obtain ⟨Kt, r₁, C₁v, C₁v₅, C₁t, -, hr₁, -, -, -, -, H⟩ := fw_pairAbove6_MFD' M
  obtain ⟨hg, hF⟩ := M.fw_atG6 hE hs hr₁ H
  obtain ⟨G₁, hG₁, hsm⟩ := M.fb_small hr₀
  have hθ : 0 ≤ 3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm := by
    have hL2 : (2 : ℝ) ≤ L := by
      exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
    obtain ⟨-, -, -, -, -, -, -, hcm, -⟩ := M.core.hC2
    have : 0 ≤ cmu ((L : ℝ) ^ 2) M.core.cm := by
      unfold cmu; have : (0 : ℝ) < (L : ℝ) ^ 2 - 1 := by nlinarith
      positivity
    positivity
  have hq : 1 ≤ 1 + 2 * |pW| * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm) := by
    have : 0 ≤ 2 * |pW| * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm) := by positivity
    linarith
  have hmin : 0 ≤ min (M.fwG6 Kt r₁ C₁v C₁v₅ C₁t) (M.core.ε / 2) := by
    by_contra hc
    exact absurd hg (not_lt.2 (div_nonpos_of_nonpos_of_nonneg (not_le.1 hc).le (by linarith)))
  have hg'ε := (div_le_self hmin hq).trans (min_le_right _ _)
  refine ⟨pW, _, M.fwK6 r₁ C₁v C₁v₅ C₁t, lt_min hg hG₁, (min_le_left _ _).trans hg'ε, hs, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm hKz b μc hb hadm hmV hgc
  exact hF N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b μc hb hadm hmV (hgc.trans (min_le_left _ _))
    (hsm N Nh m _ hm.1.le (hadm.1 Nh le_rfl).1.le (hgc.trans (min_le_right _ _)) hmV hKz)

set_option maxHeartbeats 4000000 in
/-- `fb_constsT` for a given `M`. -/
theorem eqs_constsT (M : MasterFacts L) :
    ∃ (pW g₀ K K' : ℝ), 0 < g₀ ∧ g₀ ≤ M.core.ε / 2 ∧
      pW * cmu ((L : ℝ) ^ 2) M.core.cm ≤ 1 / 12 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 3 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, M.Kp * zA L m (Nh - 1) ≤ 1 / 2 →
    ∀ b μc : ℝ, 0 < b →
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μc →
      m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ≤ g₀ → FwResT M pW K K' R Nh m b μc := by
  obtain ⟨pW, r₀, hs, hr₀, -, hE⟩ := M.fb_h0EndsGS
  obtain ⟨Kt, r₁, C₁v, C₁v₅, C₁t, -, hr₁, -, -, -, -, H⟩ := fw_pairAbove6_MFD' M
  obtain ⟨r₂, hr₂, hr₂1, hJ⟩ := M.jet
  obtain ⟨Kt₂, -, hZTl⟩ := PtCorr2.lastOut_zeroT M.zeroT
  have hcK : 0 ≤ (2 * iotaT L M.core.Cw (3 * M.core.C₁w + 1) (3 * (81 / 64) ^ 2) * M.core.A) ^ (L ^ 2) := by
    have := one_le_iotaT L M.core.Cw (3 * M.core.C₁w + 1) (by positivity : (0 : ℝ) ≤ 3 * (81 / 64) ^ 2)
    have := M.core.hA2
    positivity
  obtain ⟨hg, hF⟩ := M.fw_atGT hE hs hr₁ H hr₂ hr₂1 hJ hcK M.core.topSeedD hZTl
  obtain ⟨G₁, hG₁, hsm⟩ := M.fb_small hr₀
  have hθ : 0 ≤ 3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm := by
    have hL2 : (2 : ℝ) ≤ L := by
      exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
    obtain ⟨-, -, -, -, -, -, -, hcm, -⟩ := M.core.hC2
    have : 0 ≤ cmu ((L : ℝ) ^ 2) M.core.cm := by
      unfold cmu; have : (0 : ℝ) < (L : ℝ) ^ 2 - 1 := by nlinarith
      positivity
    positivity
  have hq : 1 ≤ 1 + 2 * |pW| * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm) := by
    have : 0 ≤ 2 * |pW| * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm) := by positivity
    linarith
  have hmin : 0 ≤ min (min (M.fwG6 Kt r₁ C₁v C₁v₅ C₁t)
      (M.fwGT Kt₂ r₂ ((2 * iotaT L M.core.Cw (3 * M.core.C₁w + 1) (3 * (81 / 64) ^ 2) *
        M.core.A) ^ (L ^ 2)))) (M.core.ε / 2) := by
    by_contra hc
    exact absurd hg (not_lt.2 (div_nonpos_of_nonpos_of_nonneg (not_le.1 hc).le (by linarith)))
  have hg'ε := (div_le_self hmin hq).trans (min_le_right _ _)
  refine ⟨pW, _, M.fwK6 r₁ C₁v C₁v₅ C₁t, M.fwKT ((2 * iotaT L M.core.Cw (3 * M.core.C₁w + 1)
    (3 * (81 / 64) ^ 2) * M.core.A) ^ (L ^ 2)) r₂, lt_min hg hG₁, (min_le_left _ _).trans hg'ε, hs, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm hKz b μc hb hadm hmV hgc
  exact hF N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b μc hb hadm hmV (hgc.trans (min_le_left _ _))
    (hsm N Nh m _ hm.1.le (hadm.1 Nh le_rfl).1.le (hgc.trans (min_le_right _ _)) hmV hKz)

set_option maxHeartbeats 4000000 in
/-- `ct_main` for a given `M`. -/
theorem eqs_ctMain (M : MasterFacts L) :
    ∃ (g₀ K : ℝ) (N₀ : ℕ), 0 < g₀ ∧ g₀ ≤ 1 ∧ 3 ≤ N₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
      m ∈ mRange L N ∧
      (∀ b ∈ ctBracket M R m βR, 0 < b ∧
        (∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧ FwPairBd6 K R (N - 2) m b ∧
        1 / βR / 5 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (N - 2)).1) ∧
      ∀ b, H0Sol M R m βR b →
        b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε →
        m * (L : ℝ) ^ (2 * N) ≤
          Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε b →
        Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε b ≤ g₀ →
        b ∈ ctBracket M R m βR := by
  obtain ⟨pW, g₀, K, hg, hgε, hs, hF⟩ := eqs_consts6 M
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
  obtain ⟨-, -, -, hε, -, -, -, -, -, -, -, hCb, -⟩ := M.core.hC2
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  set g₁ := min (g₀ / 3) (min (1 / (100 * (M.core.Cb + 1)))
    (min (1 / (M.Kp + 1)) (min 1 (M.core.ε / 8)))) with hg₁d
  have hg₁3 : g₁ ≤ g₀ / 3 := min_le_left _ _
  have hg₁C : g₁ ≤ 1 / (100 * (M.core.Cb + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hg₁K : g₁ ≤ 1 / (M.Kp + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hg₁1 : g₁ ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hg₁8 : g₁ ≤ M.core.ε / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hCg : ∀ y, 0 ≤ y → y ≤ g₁ → 100 * M.core.Cb * y ≤ 1 := fun y hy0 hy => by
    have h1 : y * (100 * (M.core.Cb + 1)) ≤ 1 := by
      have := hy.trans hg₁C
      rwa [le_div_iff₀ (by positivity)] at this
    have e : y * (100 * (M.core.Cb + 1)) = 100 * M.core.Cb * y + 100 * y := by ring
    linarith
  have hg₁0 : 0 < g₁ := lt_min (by linarith) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min one_pos (by linarith))))
  refine ⟨g₁, K, 4 + ⌈4 * M.Kp⌉₊, hg₁0, hg₁1, by omega, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβ hmass hy
  have hN2 : 2 ≤ N := by omega
  have hX0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.le (by positivity)
  have h4 : 4 * (m * (L : ℝ) ^ (2 * N)) ≤ g₁ := hmass.trans hy
  have hmR : m ∈ mRange L N := fin_mRange hL2 (by omega) hm (by linarith)
  have hKz : M.Kp * zA L m (N - 2 - 1) ≤ 1 / 2 := by
    refine fin_Kz_le hL2 hKp hm.le hN ?_
    have h1 : g₁ * (M.Kp + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hg₁K
    have h2 : M.Kp * (m * (L : ℝ) ^ (2 * N)) ≤ M.Kp * (g₁ / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) hKp
    have e : g₁ * (M.Kp + 1) = M.Kp * g₁ + g₁ := by ring
    have h3 : M.Kp * g₁ ≤ 1 := by linarith
    linarith
  have hF' := hF N R hP hi0 hRℓ hRA hRρ (by omega) (N - 2) (by omega) m hmR hKz
  have e₂ : (2 : ℝ) / βR = 1 / (βR / 2) := by field_simp
  refine ⟨hmR, ?_, fun b hsol hU hmV hgb => ?_⟩
  · intro b hb
    rw [ctBracket, e₂] at hb
    exact M.ct_bracket_g hgε hs R hP hi0 hRℓ hRA hRρ hN2 (by omega) hmR hF' hβ hmass
      (hy.trans hg₁3) (hCg _ (one_div_pos.2 hβ).le hy) b hb
  · obtain ⟨-, hby, -⟩ := hsol
    obtain ⟨-, -, hbr, -, -⟩ := M.fa_locate hs R hP hi0 hRℓ hRA hRρ hN2 (by omega) hmR hF' hU hmV
      (hgb.trans (hg₁3.trans (by linarith))) (hgb.trans hg₁8) (hCg _ (hX0.trans hmV) hgb)
    rw [hby] at hbr
    have e₁ : 1 / βR / 2 = 1 / (2 * βR) := by field_simp
    have e₃ : 2 * (1 / βR) = 2 / βR := by field_simp
    rw [e₁, e₃] at hbr
    exact hbr

set_option maxHeartbeats 4000000 in
/-- `thm_multiscale_final_h0_allB` for a given `M`. -/
theorem eqs_allB (M : MasterFacts L) :
    ∃ (g₀ K : ℝ) (N₀ : ℕ), 0 < g₀ ∧ g₀ ≤ 1 ∧ 3 ≤ N₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
      m ∈ mRange L N ∧
      (∃ b ∈ ctBracket M R m βR, H0Sol M R m βR b) ∧
      (∀ b ∈ ctBracket M R m βR, 0 < b ∧
        (∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧ FwAllBd K R (N - 2) m b ∧
        1 / βR / 5 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (N - 2)).1) ∧
      ∀ b, H0Sol M R m βR b →
        b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε →
        m * (L : ℝ) ^ (2 * N) ≤
          Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε b →
        Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε b ≤ g₀ →
        b ∈ ctBracket M R m βR := by
  obtain ⟨pW, g₀, K, K', hg, hgε, hs, hF⟩ := eqs_constsT M
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
  have hL2' : 2 ≤ L := by have := M.core.hL49; omega
  obtain ⟨-, -, -, hε, -, -, -, -, -, -, -, hCb, -⟩ := M.core.hC2
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  set g₁ := min (g₀ / 3) (min (1 / (100 * (M.core.Cb + 1)))
    (min (1 / (M.Kp + 1)) (min 1 (M.core.ε / 8)))) with hg₁d
  have hg₁3 : g₁ ≤ g₀ / 3 := min_le_left _ _
  have hg₁C : g₁ ≤ 1 / (100 * (M.core.Cb + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hg₁K : g₁ ≤ 1 / (M.Kp + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hg₁1 : g₁ ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hg₁8 : g₁ ≤ M.core.ε / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hCg : ∀ y, 0 ≤ y → y ≤ g₁ → 100 * M.core.Cb * y ≤ 1 := fun y hy0 hy => by
    have h1 : y * (100 * (M.core.Cb + 1)) ≤ 1 := by
      have := hy.trans hg₁C
      rwa [le_div_iff₀ (by positivity)] at this
    have e : y * (100 * (M.core.Cb + 1)) = 100 * M.core.Cb * y + 100 * y := by ring
    linarith
  have hg₁0 : 0 < g₁ := lt_min (by linarith) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min one_pos (by linarith))))
  refine ⟨g₁, max K K', 4 + ⌈4 * M.Kp⌉₊, hg₁0, hg₁1, by omega, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβ hmass hy
  have hN2 : 2 ≤ N := by omega
  have hX0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.le (by positivity)
  have h4 : 4 * (m * (L : ℝ) ^ (2 * N)) ≤ g₁ := hmass.trans hy
  have hmR : m ∈ mRange L N := fin_mRange hL2 (by omega) hm (by linarith)
  have hKz : M.Kp * zA L m (N - 2 - 1) ≤ 1 / 2 := by
    refine fin_Kz_le hL2 hKp hm.le hN ?_
    have h1 : g₁ * (M.Kp + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hg₁K
    have h2 : M.Kp * (m * (L : ℝ) ^ (2 * N)) ≤ M.Kp * (g₁ / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) hKp
    have e : g₁ * (M.Kp + 1) = M.Kp * g₁ + g₁ := by ring
    have h3 : M.Kp * g₁ ≤ 1 := by linarith
    linarith
  have hFT := hF N R hP hi0 hRℓ hRA hRρ (by omega) (N - 2) (by omega) m hmR hKz
  have hF6 : ∀ b μc : ℝ, 0 < b →
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε b μc →
      m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc (N - 2)).1 →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc (N - 2)).1 ≤ g₀ →
      FwRes6 M pW K R (N - 2) m b μc := fun b μc hb ha h1 h2 => by
    obtain ⟨a1, a2, a3, -⟩ := hFT b μc hb ha h1 h2
    exact ⟨a1, a2, a3⟩
  have e₂ : (2 : ℝ) / βR = 1 / (βR / 2) := by field_simp
  refine ⟨hmR, ?_, ?_, fun b hsol hU hmV hgb => ?_⟩
  · obtain ⟨⟨b, hb0, hb, hby, hD, -⟩, -⟩ := M.fa_bracket_all hgε hs R hP hi0 hRℓ hRA hRρ hN2
      (by omega) hmR hF6 hβ hmass (hy.trans hg₁3) (hCg _ (one_div_pos.2 hβ).le hy)
    refine ⟨b, ?_, hb0, hby, hD⟩
    rw [ctBracket, e₂]; exact hb
  · intro b hb
    rw [ctBracket, e₂] at hb
    obtain ⟨hb0, hD, hP1, hP2, hgl⟩ := M.ct_bracket_gT hgε hs R hP hi0 hRℓ hRA hRρ hN2 (by omega)
      hmR hFT hβ hmass (hy.trans hg₁3) (hCg _ (one_div_pos.2 hβ).le hy) b hb
    exact ⟨hb0, hD, fwAll_of hL2' R hb0 hD hP1 hP2, hgl⟩
  · obtain ⟨-, hby, -⟩ := hsol
    obtain ⟨-, -, hbr, -, -⟩ := M.fa_locate hs R hP hi0 hRℓ hRA hRρ hN2 (by omega) hmR hF6 hU hmV
      (hgb.trans (hg₁3.trans (by linarith))) (hgb.trans hg₁8) (hCg _ (hX0.trans hmV) hgb)
    rw [hby] at hbr
    have e₁ : 1 / βR / 2 = 1 / (2 * βR) := by field_simp
    have e₃ : 2 * (1 / βR) = 2 / βR := by field_simp
    rw [e₁, e₃] at hbr
    exact hbr

end

end Spin2
