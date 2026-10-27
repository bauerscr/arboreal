import Spin2.Final.FinalTop1

/-!
# The final theorem with the top coalescence scales `j_x ∈ {N − 1, N}`

`thm_multiscale_final_h0` (`Spin2/Final/FinalTheorem`) covers `x ≠ 0` with `j_x ≤ N − 2`. Here the same
chain is run with the result predicate `FwResT = FwRes6 ∧ FwTopBd` (copies of `fw_atG6`,
`fb_consts6`, `fw_bracket6`, `thm_multiscale_h0_beta6` with the threshold capped by `fwGT`):

* **`thm_multiscale_final_h0_top`**: the statement of `thm_multiscale_final_h0` and, for every
  `x ≠ 0` with `j_x ≥ N − 1`, `|P_{1/b}[0 ↔ x] − ϑ_{N−2}²| ≤ K'ϑ_{N−2}²/β_{N−2}`.
* **`thm_multiscale_final_h0_allx`**: all `x ≠ 0` at the scale `min(j_p, N − 2)`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

/-- `FwRes6` with the top bound `FwTopBd K'` added. -/
def FwResT {L : ℕ} [NeZero L] (M : MasterFacts L) (pW K K' : ℝ) {N : ℕ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ) (m b μc : ℝ) : Prop :=
  (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
    |(traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 -
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1| ≤
      pW * (2 * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1)) ∧
    (FwPairBd6 K R Nh m b ∧ FwTopBd K' R Nh m b)

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

set_option maxHeartbeats 4000000 in
/-- **`fw_atG` with the pair layer `FwPairConcl6D`** (conclusion `FwRes6`, threshold `fwG6`). -/
theorem fw_atGT {pW r₀ Kt r₁ C₁v C₁v₅ C₁t r₂ Kt₂ cK : ℝ} (hE : H0EndsConclG M pW r₀)
    (hs : pW * cmu ((L : ℝ) ^ 2) M.core.cm ≤ 1 / 12) (hr₁ : 0 < r₁)
    (H : FwPairConcl6D M Kt r₁ C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb C₁v₅ C₁t)
    (hr₂ : 0 < r₂) (hr₂1 : r₂ ≤ 1) (hJ : LastJetBd L (M.core.A / 2) r₂) (hcK : 0 ≤ cK)
    (hS : TopSeedConclD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT M.core.ε
      M.core.Cf M.core.cKL cK)
    (hZTl : ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc →
      0 ≤ R.ρ → R.ρ ≤ M.core.ρ → 0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
      ∀ (Nh : ℕ), Nh + 2 = N → ∀ t : Flow2.Hist.Seq (Xs R),
        ‖(R.msq : ℂ) * ((lastOut R Nh t).Z * zmRaw R (Nh + 1) (lastOut R Nh t).ζ) - 1‖ ≤
          Kt₂ * R.msq * (L : ℝ) ^ (2 * N)) :
    0 < min (min (M.fwG6 Kt r₁ C₁v C₁v₅ C₁t) (M.fwGT Kt₂ r₂ cK)) (M.core.ε / 2) /
      (1 + 2 * |pW| * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm)) ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 3 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μc : ℝ, 0 < b →
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μc →
      m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ≤
        min (min (M.fwG6 Kt r₁ C₁v C₁v₅ C₁t) (M.fwGT Kt₂ r₂ cK)) (M.core.ε / 2) /
        (1 + 2 * |pW| * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm)) →
      H0OnePtSmall M N Nh m r₀ (5 / 4 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1) →
      FwResT M pW (M.fwK6 r₁ C₁v C₁v₅ C₁t) (M.fwKT cK r₂) R Nh m b μc := by
  obtain ⟨-, -, -, hε, -, -, -, hcm, -⟩ := M.core.hC2
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
  have hcμ : 0 < cmu ((L : ℝ) ^ 2) M.core.cm := by
    unfold cmu; have : (0 : ℝ) < (L : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have hwin := h0_win_cond hcμ hs
  set θ := 3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm with hθd
  have hθ0 : 0 ≤ θ := by positivity
  set q := 1 + 2 * |pW| * θ with hqd
  have hq1 : 1 ≤ q := by have : 0 ≤ 2 * |pW| * θ := by positivity
                         linarith
  set G6 := min (M.fwG6 Kt r₁ C₁v C₁v₅ C₁t) (M.fwGT Kt₂ r₂ cK) with hG6d
  have hgm : 0 < min G6 (M.core.ε / 2) :=
    lt_min (lt_min (M.fwG6_pos hr₁) (M.fwGT_pos hr₂)) (by linarith)
  refine ⟨div_pos hgm (by linarith), ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b μc hb hadm hmV hgc hsm
  have hN2 : 2 ≤ N := by omega
  set gc := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 with hgcd
  have hgc0 : 0 ≤ gc := (hadm.1 Nh le_rfl).1.le
  have hgq : gc * q ≤ min G6 (M.core.ε / 2) := by
    rwa [le_div_iff₀ (by linarith)] at hgc
  have hpq : 1 + 2 * pW * θ ≤ q := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self pW)
      (by norm_num : (0 : ℝ) ≤ 2)) hθ0
    linarith
  have hgy : gc * (1 + 2 * pW * θ) < M.core.ε := by
    have := mul_le_mul_of_nonneg_left hpq hgc0
    have := min_le_right G6 (M.core.ε / 2)
    linarith
  have hcard : (Fintype.card (Lam 2 L N) : ℝ) = (L : ℝ) ^ (2 * N) := by
    rw [show Fintype.card (Lam 2 L N) = (L ^ N) ^ 2 from FRD.card_torus]; push_cast; ring
  obtain ⟨μl, μu, -, -, -, -, -, -, -, hD0, -, hgd⟩ := hE N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm
    b μc hb hadm (by rw [hcard]; exact hmV) hwin hgy hsm
  have e : ∀ x : ℝ, pW * (x - -x) = pW * (2 * x) := fun x => by ring
  refine ⟨hD0, by rw [← e]; exact hgd, ?_⟩
  have hG : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ G6 := by
    have h1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 - gc ≤
        pW * (θ * gc - -(θ * gc)) := (abs_le.1 hgd).2
    have h2 : pW * (θ * gc - -(θ * gc)) ≤ |pW| * (θ * gc - -(θ * gc)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by have := mul_nonneg hθ0 hgc0; linarith)
    have e : gc * q = gc + |pW| * (θ * gc - -(θ * gc)) := by rw [hqd]; ring
    have := min_le_left G6 (M.core.ε / 2)
    linarith
  have hmΛ : m * (L : ℝ) ^ (2 * N) ≤ G6 := by
    have := min_le_left G6 (M.core.ε / 2)
    have hgq' : gc ≤ gc * q := le_mul_of_one_le_right hgc0 hq1
    linarith
  refine ⟨fun x hx hj => M.fw_multiscale_traj6 H R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD0
    ((hG.trans (min_le_left _ _)).trans (min_le_left _ _)) (hmΛ.trans (min_le_left _ _)) x hx hj, ?_⟩
  exact M.fw_top_trajG hr₂ hr₂1 hJ hcK hS hZTl R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD0
    (hG.trans (min_le_right _ _)) (hmΛ.trans (min_le_right _ _))

end MasterFacts

set_option maxHeartbeats 4000000 in
/-- **The constants of the final theorem with the top bound** (copy of `fb_consts6`):
`g₀ = min(g₀(fw_atG6), G₁)`, pair constant `K = fwK6`. -/
theorem fb_constsT : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (pW g₀ K K' : ℝ), 0 < g₀ ∧ g₀ ≤ M.core.ε / 2 ∧
      pW * cmu ((L : ℝ) ^ 2) M.core.cm ≤ 1 / 12 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 3 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, M.Kp * zA L m (Nh - 1) ≤ 1 / 2 →
    ∀ b μc : ℝ, 0 < b →
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μc →
      m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ≤ g₀ → FwResT M pW K K' R Nh m b μc := by
  obtain ⟨L₀, h⟩ := thm_master_all
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M⟩ := h L hL
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
  refine ⟨M, pW, _, M.fwK6 r₁ C₁v C₁v₅ C₁t, M.fwKT ((2 * iotaT L M.core.Cw (3 * M.core.C₁w + 1)
    (3 * (81 / 64) ^ 2) * M.core.A) ^ (L ^ 2)) r₂, lt_min hg hG₁, (min_le_left _ _).trans hg'ε, hs, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm hKz b μc hb hadm hmV hgc
  exact hF N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b μc hb hadm hmV (hgc.trans (min_le_left _ _))
    (hsm N Nh m _ hm.1.le (hadm.1 Nh le_rfl).1.le (hgc.trans (min_le_right _ _)) hmV hKz)

set_option maxHeartbeats 4000000 in
/-- **`fw_bracket6` with `FwResT`.** -/
theorem MasterFacts.fw_bracketT {L : ℕ} [NeZero L] (M : MasterFacts L) {pW g₀ K K' : ℝ}
    (hgε : g₀ ≤ M.core.ε / 2) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hF : ∀ b μc : ℝ, 0 < b →
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μc →
      m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ≤ g₀ → FwResT M pW K K' R Nh m b μc)
    (hm : m ∈ mRange L N) {b₁ b₂ μ₁ μ₂ y : ℝ}
    (hb₁ : 0 < b₁) (hb12 : b₁ ≤ b₂)
    (ha₁ : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b₁ μ₁)
    (ha₂ : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b₂ μ₂)
    (hm₁ : m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁ Nh).1)
    (hg₂ : (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1 ≤ g₀)
    (hy₁ : gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁) +
          (pW * (2 * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm *
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁ Nh).1)) +
            2 * M.core.Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ (b₁ - m) Nh).1 ^ 2 +
            2 * M.core.Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁ Nh).1 ^ 2) ≤ y)
    (hy₂ : y ≤ gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂) -
          (pW * (2 * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm *
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1)) +
            2 * M.core.Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ (b₂ - m) Nh).1 ^ 2 +
            2 * M.core.Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1 ^ 2)) :
    ∃ b ∈ Icc b₁ b₂, gFinH0 R Nh m b = y ∧
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
      (FwPairBd6 K R Nh m b ∧ FwTopBd K' R Nh m b) := by
  obtain ⟨-, -, -, hε, -, -, -, -, -, -, -, -, -, -, -, H⟩ := M.core.hC2
  obtain ⟨hfc, -⟩ := H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh
  have fc := hfc m hm
  have hg₂ε : (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1 < M.core.ε := by linarith
  have hBe := fun b (hb : b ∈ Icc b₁ b₂) => fb_ufix_between fc ha₁ ha₂ hg₂ε hb
  obtain ⟨-, h1, h2⟩ := hBe b₁ ⟨le_rfl, hb12⟩
  have hb₂ : 0 < b₂ := hb₁.trans_le hb12
  obtain ⟨hD₁, hd₁, -⟩ := hF b₁ μ₁ hb₁ ha₁ hm₁ (by linarith)
  obtain ⟨hD₂, hd₂, -⟩ := hF b₂ μ₂ hb₂ ha₂ (by linarith) hg₂
  obtain ⟨b, hb, hby⟩ := M.core.h0Shoot R hP hi0 hRℓ hRA hRρ hN2 hNh hm hb12 ha₁ ha₂ hD₁ hD₂
    hd₁ hd₂ hy₁ hy₂
  obtain ⟨ham, hl, hu⟩ := hBe b hb
  obtain ⟨hD, -, hPb⟩ := hF b _ (hb₁.trans_le hb.1) ham (hm₁.trans hl) (hu.trans hg₂)
  exact ⟨b, hb, hby, hD, hPb⟩

set_option maxHeartbeats 4000000 in
/-- **`thm_multiscale_h0_beta6` with the top bound** (constants of `fb_constsT`). -/
theorem thm_multiscale_h0_betaT : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (pW g₀ K K' : ℝ), 0 < g₀ ∧ g₀ ≤ M.core.ε / 2 ∧
      pW * cmu ((L : ℝ) ^ 2) M.core.cm ≤ 1 / 12 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 3 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, M.Kp * zA L m (Nh - 1) ≤ 1 / 2 →
    ∀ βR : ℝ, 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ / 3 →
      100 * M.core.Cb * (1 / βR) ≤ 1 →
    ∃ b, 0 < b ∧
      b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (2 * βR)))
        (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (βR / 2))) ∧
      gFinH0 R Nh m b = 1 / βR ∧
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
      (FwPairBd6 K R Nh m b ∧ FwTopBd K' R Nh m b) := by
  obtain ⟨L₀, h⟩ := fb_constsT
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, pW, g₀, K, K', hg, hgε, hs, hF⟩ := h L hL
  refine ⟨M, pW, g₀, K, K', hg, hgε, hs, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm hKz βR hβ hmass hyg hcy
  have hN2 : 2 ≤ N := by omega
  have hF' := hF N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm hKz
  obtain ⟨-, -, -, hε, -, -, -, -, -, -, -, hCb, -, -, -, H⟩ := M.core.hC2
  obtain ⟨hfc, -, -, -, -, hnear, hsm, -, hbF, -⟩ := H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh
  have fc := hfc m hm
  have hy : 0 < 1 / βR := one_div_pos.2 hβ
  have h6 : 6 ≤ M.core.ε * βR := by
    have : 1 / βR ≤ M.core.ε / 6 := by linarith
    rw [div_le_iff₀ hβ] at this
    linarith
  have e₁ : 1 / (2 * βR) = 1 / βR / 2 := by field_simp
  have e₂ : 1 / (βR / 2) = 2 * (1 / βR) := by field_simp
  obtain ⟨U₁, G₁⟩ := (hbF (2 * βR) (by rw [div_le_iff₀ hε]; linarith)).1 m hm
  obtain ⟨U₂, G₂⟩ := (hbF (βR / 2) (by rw [div_le_iff₀ hε]; linarith)).1 m hm
  set b₁ := bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (2 * βR)) with hb₁d
  set b₂ := bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (βR / 2)) with hb₂d
  have N₁ := hnear m hm b₁ U₁ (2 * βR) G₁
  have N₂ := hnear m hm b₂ U₂ (βR / 2) G₂
  rw [e₁] at N₁ G₁
  rw [e₂] at N₂ G₂
  have ha₁ := fb_adm_muc U₁.choose_spec.1
  have ha₂ := fb_adm_muc U₂.choose_spec.1
  set μ₁ := Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b₁
  set μ₂ := Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b₂
  have hb12 : b₁ ≤ b₂ := by
    by_contra hc
    have := hsm m hm U₂ U₁ (not_le.1 hc)
    rw [G₁, G₂] at this
    linarith
  have hb₁ : 0 < b₁ := (ha₁.1 0 (Nat.zero_le _)).1
  have hb₂ : 0 < b₂ := hb₁.trans_le hb12
  set g₁ := (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁ Nh).1 with hg₁d
  set g₂ := (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1 with hg₂d
  have hg₁0 : 0 ≤ g₁ := (ha₁.1 Nh le_rfl).1.le
  have hg₂0 : 0 ≤ g₂ := (ha₂.1 Nh le_rfl).1.le
  have N₁' : |g₁ - 1 / βR / 2| ≤ 4 * M.core.Cb * (1 / βR / 2) ^ 2 := N₁
  have N₂' : |g₂ - 2 * (1 / βR)| ≤ 4 * M.core.Cb * (2 * (1 / βR)) ^ 2 := N₂
  have hs₁ := fb_s_le hs hg₁0
  have hs₂ := fb_s_le hs hg₂0
  have hcy' : 100 * M.core.Cb * (1 / βR) ≤ 1 := hcy
  -- the upper end: `ǧ^c(b₂) ≤ 3y ≤ g₀`
  have hgu₂ : g₂ ≤ 3 * (1 / βR) := by
    have hcy2 : M.core.Cb * (1 / βR) ^ 2 ≤ 1 / βR / 100 := by
      have := mul_le_mul_of_nonneg_right (show M.core.Cb * (1 / βR) ≤ 1 / 100 by linarith) hy.le
      calc M.core.Cb * (1 / βR) ^ 2 = M.core.Cb * (1 / βR) * (1 / βR) := by ring
        _ ≤ 1 / 100 * (1 / βR) := this
        _ = 1 / βR / 100 := by ring
    have e : 4 * M.core.Cb * (2 * (1 / βR)) ^ 2 = 16 * (M.core.Cb * (1 / βR) ^ 2) := by ring
    have := (abs_le.1 N₂').2
    linarith
  have hg₂g : g₂ ≤ g₀ := by linarith
  -- the lower end: `y/4 ≤ ǧ^c(b₁)`
  have hgl₁ : 1 / βR / 4 ≤ g₁ := by
    have hcy2 : M.core.Cb * (1 / βR) ^ 2 ≤ 1 / βR / 100 := by
      have := mul_le_mul_of_nonneg_right (show M.core.Cb * (1 / βR) ≤ 1 / 100 by linarith) hy.le
      calc M.core.Cb * (1 / βR) ^ 2 = M.core.Cb * (1 / βR) * (1 / βR) := by ring
        _ ≤ 1 / 100 * (1 / βR) := this
        _ = 1 / βR / 100 := by ring
    have e : 4 * M.core.Cb * (1 / βR / 2) ^ 2 = M.core.Cb * (1 / βR) ^ 2 := by ring
    have := (abs_le.1 N₁').1
    linarith
  have hm₁ : m * (L : ℝ) ^ (2 * N) ≤ g₁ := by linarith
  have hg₁g : g₁ ≤ g₀ := by
    obtain ⟨-, h1, h2⟩ := fb_ufix_between fc ha₁ ha₂ (by linarith) ⟨le_rfl, hb12⟩
    linarith
  -- the end distances
  obtain ⟨-, hd₁, -⟩ := hF' b₁ _ hb₁ ha₁ hm₁ hg₁g
  obtain ⟨-, hd₂, -⟩ := hF' b₂ _ hb₂ ha₂ (by
    obtain ⟨-, h1, h2⟩ := fb_ufix_between fc ha₁ ha₂ (by linarith) ⟨le_rfl, hb12⟩
    linarith) hg₂g
  have hy₁ := (fb_margin_lo hCb hy hcy' hg₁0 N₁' hs₁ hd₁).1
  have hy₂ := (fb_margin_hi hCb hy hcy' hg₂0 N₂' hs₂ hd₂).1
  have G₁' : gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁) = 1 / βR / 2 := G₁
  have G₂' : gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂) = 2 * (1 / βR) := G₂
  obtain ⟨b, hb, hby, hD, hPb⟩ := M.fw_bracketT hgε R hP hi0 hRℓ hRA hRρ hN2 hNh hF' hm hb₁ hb12
    ha₁ ha₂ hm₁ hg₂g (y := 1 / βR)
    (by rw [G₁']; linarith) (by rw [G₂']; linarith)
  exact ⟨b, hb₁.trans_le hb.1, hb, hby, hD, hPb⟩

set_option maxHeartbeats 4000000 in
/-- **Theorem `thm:multiscale` (outline) at `h = 0` with the top coalescence scales.**
The statement of `thm_multiscale_final_h0` and, in addition, for every `x ≠ 0` with
`j_x ≥ N − 1` (`j_x ∈ {N − 1, N}`): `|P_{1/b}[0 ↔ x] − ϑ_{N−2}²| ≤ K'ϑ_{N−2}²/β_{N−2}`.
Original docstring: **Theorem `thm:multiscale` (outline) at `h = 0`, at the shooting value `β_ε = 1/b`.**
For `L ≥ L₀` there are the master construction `M`, `g₀ > 0`, `K` and `N₀` such that for
`N ≥ N₀`, every auxiliary mass `m² > 0` and every `β_R > 0` with `4m²L^{2N} ≤ 1/β_R ≤ g₀`, there is
`b > 0` with `Re ǧ_N(b, b − m²) = 1/β_R` (the renormalised coupling at the last scale is `1/β_R`), the
`h = 0` trajectory `(ǧ_j, μ_j)` from `(b, b − m²)` stays in `D_ε` up to `N − 2`, and for every
`x ≠ 0` with coalescence scale `j_x ≤ N − 2` and physical scale `j` of `x`
(`j ≤ j_x ≤ j + 1`): `|P_{1/b}[0 ↔ x] − ϑ_j²| ≤ K ϑ_j²/β_j`.
No hypotheses beyond the stated ranges. -/
theorem thm_multiscale_final_h0_top : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ K K' : ℝ) (N₀ : ℕ), 0 < g₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
    ∃ b, 0 < b ∧ gFinH0 R (N - 2) m b = 1 / βR ∧
      (∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
      (∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ N - 2 →
        ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
          jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
          |Pconn L N (1 / b) x - thetaSq R m b (b - m) jp| ≤
            K * thetaSq R m b (b - m) jp / betaJ R m b (b - m) jp) ∧
      ∀ x : Lam 2 L N, x ≠ 0 → N - 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
        |Pconn L N (1 / b) x - thetaSq R m b (b - m) (N - 2)| ≤
          K' * thetaSq R m b (b - m) (N - 2) / betaJ R m b (b - m) (N - 2) := by
  obtain ⟨L₀, h⟩ := thm_multiscale_h0_betaT
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, pW, g₀, K, K', hg, hgε, -, hF⟩ := h L hL
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hCb, -⟩ := M.core.hC2
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  set g₁ := min (g₀ / 3) (min (1 / (100 * (M.core.Cb + 1))) (min (1 / (M.Kp + 1)) 1)) with hg₁d
  refine ⟨M, g₁, K, K', 4 + ⌈4 * M.Kp⌉₊, ?_, ?_⟩
  · refine lt_min (by linarith) (lt_min (by positivity) (lt_min (by positivity) one_pos))
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβ hmass hy
  set y := 1 / βR with hyd
  have hy0 : 0 < y := one_div_pos.2 hβ
  have hX0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.le (by positivity)
  have hyg : y ≤ g₀ / 3 := hy.trans (min_le_left _ _)
  have hyC : y ≤ 1 / (100 * (M.core.Cb + 1)) := hy.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hyK : y ≤ 1 / (M.Kp + 1) :=
    hy.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hy1 : y ≤ 1 :=
    hy.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hcy : 100 * M.core.Cb * (1 / βR) ≤ 1 := by
    rw [← hyd]
    have h1 : y * (100 * (M.core.Cb + 1)) ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at hyC
    nlinarith
  have hmR : m ∈ mRange L N := fin_mRange hL2 (by omega) hm (by linarith)
  have hKz : M.Kp * zA L m (N - 2 - 1) ≤ 1 / 2 := by
    refine fin_Kz_le hL2 hKp hm.le hN ?_
    have h1 : y * (M.Kp + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hyK
    have h2 : M.Kp * (m * (L : ℝ) ^ (2 * N)) ≤ M.Kp * (y / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) hKp
    nlinarith
  obtain ⟨b, hb, -, hby, hD, hPb, hTb⟩ := hF N R hP hi0 hRℓ hRA hRρ (by omega) (N - 2) (by omega) m
    hmR hKz βR hβ hmass hyg hcy
  exact ⟨b, hb, hby, hD, hPb, fun x hx hj => hTb x hx (by omega)⟩

/-- **Theorem `thm:multiscale` at `h = 0` for all `x ≠ 0`**: with the physical scale `j_p` of `x`,
`|P_{1/b}[0 ↔ x] − ϑ_k²| ≤ Kϑ_k²/β_k` at `k = min(j_p, N − 2)` (`j_p ≤ j_x ≤ j_p + 1`). -/
theorem thm_multiscale_final_h0_allx : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ K : ℝ) (N₀ : ℕ), 0 < g₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
    ∃ b, 0 < b ∧ gFinH0 R (N - 2) m b = 1 / βR ∧
      (∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
      ∀ x : Lam 2 L N, x ≠ 0 →
        ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
          jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
          |Pconn L N (1 / b) x - thetaSq R m b (b - m) (min jp (N - 2))| ≤
            K * thetaSq R m b (b - m) (min jp (N - 2)) / betaJ R m b (b - m) (min jp (N - 2)) := by
  obtain ⟨L₀, h⟩ := thm_multiscale_final_h0_top
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, g₀, K, K', N₀, hg, hF⟩ := h L hL
  refine ⟨M, g₀, max K K', N₀, hg, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβ hmass hy
  obtain ⟨b, hb, hby, hD, hP1, hP2⟩ := hF N R hP hi0 hRℓ hRA hRρ hN m βR hm hβ hmass hy
  refine ⟨b, hb, hby, hD, fun x hx => ?_⟩
  have hnn : ∀ k ≤ N - 2, 0 ≤ thetaSq R m b (b - m) k / betaJ R m b (b - m) k := fun k hk => by
    have hg := (hD k hk).1
    unfold thetaSq betaJ
    exact div_nonneg (Real.rpow_nonneg (div_nonneg (one_div_pos.2 hg).le
      (one_div_pos.2 hb).le) _) (one_div_pos.2 hg).le
  rcases Nat.lt_or_ge (Obs.coal L (0 : Lam 2 L N) x) (N - 1) with hc | hc
  · obtain ⟨jp, h1, h2, h3, h4⟩ := hP1 x hx (by omega)
    refine ⟨jp, h1, h2, h3, ?_⟩
    rw [min_eq_left (by omega)]
    refine h4.trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn jp (by omega))
  · have hL2 : 2 ≤ L := by have := M.core.hL49; omega
    obtain ⟨jp, h1, h2, h3⟩ := coal_jPhys hL2 hx
    refine ⟨jp, h1, h2, h3, ?_⟩
    rw [min_eq_right (by omega)]
    refine (hP2 x hx hc).trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (hnn (N - 2) le_rfl)

end

end Spin2
