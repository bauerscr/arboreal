import Spin2.Final.FinalTheorem

/-!
# `thm:multiscale` at `h = 0` for every solution in the bracket, and per `b`

`thm_multiscale_final_h0` gives *one* `b` with `Re ǧ_N(b, b − m²) = 1/β_R` at which the pair bound
holds. Here:

* **`H0Sol`**: `b > 0` solves the `h = 0` shooting problem `Re ǧ_N(b, b − m²) = 1/β_R` with the
  `h = 0` trajectory in `D_ε` up to `N − 2`; **`thetaEpsSq`** `= (β_R b)^{2/3}`.
* **`MasterFacts.fa_bracket_all`** (`thm_multiscale_h0_beta6` extended): on the whole bracket
  `[bFin(y/2), bFin(2y)]`, `y = 1/β_R`, (not only at the shooting solution) the `h = 0` trajectory
  is in `D_ε` and `FwPairBd6` holds (`fb_ufix_between` + `FwRes6`).
* **`MasterFacts.fa_locate`**: every `b ∈ U_fix` with `m²L^{2N} ≤ ǧ^c_{N_h}(b) ≤ g₀`,
  `ǧ^c ≤ ε/8`, `100C_bǧ^c ≤ 1` lies in the bracket of its own value `y = Re ǧ_N(b, b − m²)`
  (`|y − Re ǧ^c_N(b)| ≤ s + 2C_b((ǧ^0)² + (ǧ^c)²)`, `ǧ^c ≈ Re ǧ^c_N` (`BandOut`), strict
  monotonicity of `gFinB` on `U_fix`); `y ∈ [4ǧ^c/5, 6ǧ^c/5]`.
* **`fa_main`**, **`thm_multiscale_final_h0_all`**, **`thm_multiscale_h0_perb`**: the final
  statements (constants depending on `L` only).

**A priori localisation.** "Every `H0Sol` lies in the bracket" is proved under the additional
hypotheses `b ∈ U_fix`, `m²L^{2N} ≤ ǧ^c_{N_h}(b) ≤ g₀`: the comparison `ǧ^0 ≈ ǧ^c` of the
`h = 0` window (`H0EndsConclG`) is only available for `(b, μ^c(b))` admissible with `ǧ^c` small
and above the mass scale; for `b ∉ U_fix` or `ǧ^c(b)` large there is no comparison (and no
monotonicity of `gFinH0`) in the library.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

/-- **A solution of the `h = 0` shooting problem** at `β_R`: `b > 0`, `Re ǧ_N(b, b − m²) = 1/β_R`,
and the `h = 0` trajectory from `(b, b − m²)` in `D_ε` up to `N − 2`. -/
def H0Sol {L : ℕ} [NeZero L] (M : MasterFacts L) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (m βR b : ℝ) : Prop :=
  0 < b ∧ gFinH0 R (N - 2) m b = 1 / βR ∧
    ∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)

/-- `ϑ_ε² = (β_R b)^{2/3}`. -/
def thetaEpsSq (βR b : ℝ) : ℝ := (βR * b) ^ (2 / 3 : ℝ)

/-- The arithmetic of the localisation. -/
theorem fa_arith {c g g0 s Gc y : ℝ} (hc : 0 ≤ c) (hg : 0 < g) (hcg : 100 * c * g ≤ 1)
    (hs : s ≤ g / 8) (hd : |g0 - g| ≤ s) (hG : |Gc - g| ≤ 2 * c * g ^ 2)
    (hy : |y - Gc| ≤ s + 2 * c * g0 ^ 2 + 2 * c * g ^ 2) :
    4 / 5 * g ≤ y ∧ y ≤ 6 / 5 * g ∧ y / 2 < Gc ∧ Gc < 2 * y := by
  have h1 : c * g ^ 2 ≤ g / 100 := by
    have := mul_le_mul_of_nonneg_right (show c * g ≤ 1 / 100 by linarith) hg.le
    calc c * g ^ 2 = c * g * g := by ring
      _ ≤ 1 / 100 * g := this
      _ = g / 100 := by ring
  obtain ⟨h00, h01⟩ := fb_g0_bd hg.le hs hd
  have hq : g0 ^ 2 ≤ (9 / 8 * g) ^ 2 := pow_le_pow_left₀ h00 h01 2
  have k := mul_le_mul_of_nonneg_left hq hc
  have e : c * (9 / 8 * g) ^ 2 = 81 / 64 * (c * g ^ 2) := by ring
  have hG' := abs_le.1 hG
  have hy' := abs_le.1 hy
  have hd' := abs_le.1 hd
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

set_option maxHeartbeats 4000000 in
/-- **`thm_multiscale_h0_beta6` on the whole bracket**: besides the shooting solution, at every
`b ∈ [bFin(1/(2β_R)), bFin(2/β_R)]` the `h = 0` trajectory is in `D_ε` and `FwPairBd6` holds. -/
theorem fa_bracket_all {pW g₀ K : ℝ} (hgε : g₀ ≤ M.core.ε / 2)
    (hs : pW * cmu ((L : ℝ) ^ 2) M.core.cm ≤ 1 / 12) {N : ℕ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N)
    {m : ℝ} (hm : m ∈ mRange L N)
    (hF' : ∀ b μc : ℝ, 0 < b →
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μc →
      m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ≤ g₀ → FwRes6 M pW K R Nh m b μc)
    {βR : ℝ} (hβ : 0 < βR) (hmass : 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR)
    (hyg : 1 / βR ≤ g₀ / 3) (hcy : 100 * M.core.Cb * (1 / βR) ≤ 1) :
    (∃ b, 0 < b ∧
      b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (2 * βR)))
        (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (βR / 2))) ∧
      gFinH0 R Nh m b = 1 / βR ∧
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
      FwPairBd6 K R Nh m b) ∧
    ∀ b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (2 * βR)))
        (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (βR / 2))),
      0 < b ∧ (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧ FwPairBd6 K R Nh m b := by
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
  have hcy2 : M.core.Cb * (1 / βR) ^ 2 ≤ 1 / βR / 100 := by
    have := mul_le_mul_of_nonneg_right (show M.core.Cb * (1 / βR) ≤ 1 / 100 by linarith) hy.le
    calc M.core.Cb * (1 / βR) ^ 2 = M.core.Cb * (1 / βR) * (1 / βR) := by ring
      _ ≤ 1 / 100 * (1 / βR) := this
      _ = 1 / βR / 100 := by ring
  have hgu₂ : g₂ ≤ 3 * (1 / βR) := by
    have e : 4 * M.core.Cb * (2 * (1 / βR)) ^ 2 = 16 * (M.core.Cb * (1 / βR) ^ 2) := by ring
    have := (abs_le.1 N₂').2
    linarith
  have hg₂g : g₂ ≤ g₀ := by linarith
  have hg₂ε : g₂ < M.core.ε := by linarith
  have hgl₁ : 1 / βR / 4 ≤ g₁ := by
    have e : 4 * M.core.Cb * (1 / βR / 2) ^ 2 = M.core.Cb * (1 / βR) ^ 2 := by ring
    have := (abs_le.1 N₁').1
    linarith
  have hm₁ : m * (L : ℝ) ^ (2 * N) ≤ g₁ := by linarith
  have hBe := fun b (hb : b ∈ Icc b₁ b₂) => fb_ufix_between fc ha₁ ha₂ hg₂ε hb
  have hg₁g : g₁ ≤ g₀ := by
    obtain ⟨-, h1, h2⟩ := hBe b₁ ⟨le_rfl, hb12⟩
    linarith
  have hAll : ∀ b ∈ Icc b₁ b₂, 0 < b ∧ (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm
      M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
      FwPairBd6 K R Nh m b := fun b hb => by
    obtain ⟨ham, hl, hu⟩ := hBe b hb
    obtain ⟨hD, -, hPb⟩ := hF' b _ (hb₁.trans_le hb.1) ham (hm₁.trans hl) (hu.trans hg₂g)
    exact ⟨hb₁.trans_le hb.1, hD, hPb⟩
  refine ⟨?_, hAll⟩
  obtain ⟨-, hd₁, -⟩ := hF' b₁ _ hb₁ ha₁ hm₁ hg₁g
  obtain ⟨-, hd₂, -⟩ := hF' b₂ _ hb₂ ha₂ (by
    obtain ⟨-, h1, h2⟩ := hBe b₁ ⟨le_rfl, hb12⟩
    linarith) hg₂g
  have hy₁ := (fb_margin_lo hCb hy hcy hg₁0 N₁' hs₁ hd₁).1
  have hy₂ := (fb_margin_hi hCb hy hcy hg₂0 N₂' hs₂ hd₂).1
  have G₁' : gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁) = 1 / βR / 2 := G₁
  have G₂' : gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂) = 2 * (1 / βR) := G₂
  obtain ⟨b, hb, hby, hD, hPb⟩ := M.fw_bracket6 hgε R hP hi0 hRℓ hRA hRρ hN2 hNh hF' hm hb₁ hb12
    ha₁ ha₂ hm₁ hg₂g (y := 1 / βR)
    (by rw [G₁']; linarith) (by rw [G₂']; linarith)
  exact ⟨b, hb₁.trans_le hb.1, hb, hby, hD, hPb⟩

set_option maxHeartbeats 4000000 in
/-- **Localisation of a `b` in its own bracket.** If `b ∈ U_fix` and
`m²L^{2N} ≤ ǧ^c_{N_h}(b) ≤ g₀`, `ǧ^c ≤ ε/8`, `100C_bǧ^c ≤ 1`, then `y := Re ǧ_N(b, b − m²)`
satisfies `4ǧ^c/5 ≤ y` (so `y > 0`), `b ∈ [bFin(y/2), bFin(2y)]`, and the `h = 0` trajectory is
in `D_ε` with `FwPairBd6` at `b`. -/
theorem fa_locate {pW g₀ K : ℝ} (hs : pW * cmu ((L : ℝ) ^ 2) M.core.cm ≤ 1 / 12) {N : ℕ}
    (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ}
    (hNh : Nh + 2 = N) {m : ℝ} (hm : m ∈ mRange L N)
    (hF' : ∀ b μc : ℝ, 0 < b →
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μc →
      m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ≤ g₀ → FwRes6 M pW K R Nh m b μc)
    {b : ℝ} (hU : b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε)
    (hmV : m * (L : ℝ) ^ (2 * N) ≤
      Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b)
    (hg : Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b ≤ g₀)
    (hg8 : Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b ≤
      M.core.ε / 8)
    (hgC : 100 * M.core.Cb *
      Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b ≤ 1) :
    4 / 5 * Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b ≤
        gFinH0 R Nh m b ∧ 0 < gFinH0 R Nh m b ∧
      b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (gFinH0 R Nh m b / 2))
        (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (2 * gFinH0 R Nh m b)) ∧
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧ FwPairBd6 K R Nh m b := by
  obtain ⟨-, -, -, hε, -, -, -, -, -, -, -, hCb, -, -, -, H⟩ := M.core.hC2
  obtain ⟨-, -, -, -, -, -, hsm, -, hbF, -⟩ := H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh
  have hU' := hU
  obtain ⟨μ, ha, -⟩ := hU'
  have ham := fb_adm_muc ha
  have hb : 0 < b := (ha.1 0 (Nat.zero_le _)).1
  set g := Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b
    with hgd
  have eg : g = (traj (rgDataM R m) ((L : ℝ) ^ 2) b
      (Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b) Nh).1 :=
    rfl
  have hg0 : 0 < g := by rw [eg]; exact (ham.1 Nh le_rfl).1
  obtain ⟨hD, hd, hPb⟩ := hF' b _ hb ham (by rw [← eg]; exact hmV) (by rw [← eg]; exact hg)
  rw [← eg] at hd
  have G0 := (M.core.hGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD).2
  have Gc := (M.core.hGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b _ ham.1).2
  have hband : |gFinB R M.core.κ M.core.cm M.core.cT Nh M.core.ε m b - g| ≤
      2 * M.core.Cb * g ^ 2 := Gc.gFin_sub
  have hnear : |gFinH0 R Nh m b - gFinB R M.core.κ M.core.cm M.core.cT Nh M.core.ε m b| ≤
      pW * (2 * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm * g)) +
        2 * M.core.Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2 +
        2 * M.core.Cb * g ^ 2 := gFinH0_near R G0 Gc hd
  have key := fa_arith hCb hg0 hgC (fb_s_le hs hg0.le) hd hband hnear
  set y := gFinH0 R Nh m b with hyd
  obtain ⟨hy45, hy65, hlo, hhi⟩ := key
  have hy0 : 0 < y := by linarith
  have h4y : 4 * y ≤ M.core.ε := by linarith
  obtain ⟨U₁, G₁⟩ := (hbF (2 / y) (by rw [div_le_div_iff₀ hε hy0]; linarith)).1 m hm
  obtain ⟨U₂, G₂⟩ := (hbF (1 / (2 * y))
    (by rw [div_le_div_iff₀ hε (by linarith : (0 : ℝ) < 2 * y)]; linarith)).1 m hm
  rw [one_div_div] at U₁ G₁
  rw [one_div_one_div] at U₂ G₂
  refine ⟨hy45, hy0, ⟨?_, ?_⟩, hD, hPb⟩
  · by_contra hc
    have := hsm m hm hU U₁ (not_le.1 hc)
    rw [G₁] at this
    linarith
  · by_contra hc
    have := hsm m hm U₂ hU (not_le.1 hc)
    rw [G₂] at this
    linarith

end MasterFacts

set_option maxHeartbeats 4000000 in
/-- **The combined statement** (constants depending on `L` only): for `N ≥ N₀`, `m² > 0`,
(i) for `4m²L^{2N} ≤ 1/β_R ≤ g₀`: the shooting solution exists in the bracket
`[bFin(1/(2β_R)), bFin(2/β_R)]`, and at **every** `b` of the bracket the `h = 0` trajectory is in
`D_ε` with the pair bound; (ii) if `4m²L^{2N} ≤ g₀`, every `b ∈ U_fix` with
`m²L^{2N} ≤ ǧ^c_{N−2}(b) ≤ g₀` lies in the bracket of `y = Re ǧ_N(b, b − m²)` (`y ≥ 4ǧ^c/5 > 0`)
and satisfies the pair bound. -/
theorem fa_main : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ K : ℝ) (N₀ : ℕ), 0 < g₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m : ℝ, 0 < m →
      (∀ βR : ℝ, 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
        (∃ b, 0 < b ∧
          b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (1 / (2 * βR)))
            (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (1 / (βR / 2))) ∧
          gFinH0 R (N - 2) m b = 1 / βR ∧
          (∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
          FwPairBd6 K R (N - 2) m b) ∧
        ∀ b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (1 / (2 * βR)))
            (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (1 / (βR / 2))),
          0 < b ∧ (∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧ FwPairBd6 K R (N - 2) m b) ∧
      (4 * (m * (L : ℝ) ^ (2 * N)) ≤ g₀ →
        ∀ b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε,
        m * (L : ℝ) ^ (2 * N) ≤
          Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε b →
        Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε b ≤ g₀ →
        4 / 5 * Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2)
            M.core.ε b ≤ gFinH0 R (N - 2) m b ∧ 0 < gFinH0 R (N - 2) m b ∧
          b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m
              (gFinH0 R (N - 2) m b / 2))
            (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (2 * gFinH0 R (N - 2) m b)) ∧
          (∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧ FwPairBd6 K R (N - 2) m b) := by
  obtain ⟨L₀, h⟩ := fb_consts6
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, pW, g₀, K, hg, hgε, hs, hF⟩ := h L hL
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
  refine ⟨M, g₁, K, 4 + ⌈4 * M.Kp⌉₊, hg₁0, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m hm
  have hN2 : 2 ≤ N := by omega
  have hX0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.le (by positivity)
  have hMK : 4 * (m * (L : ℝ) ^ (2 * N)) ≤ g₁ →
      m ∈ mRange L N ∧ M.Kp * zA L m (N - 2 - 1) ≤ 1 / 2 := fun h4 => by
    refine ⟨fin_mRange hL2 (by omega) hm (by linarith), fin_Kz_le hL2 hKp hm.le hN ?_⟩
    have h1 : g₁ * (M.Kp + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hg₁K
    have h2 : M.Kp * (m * (L : ℝ) ^ (2 * N)) ≤ M.Kp * (g₁ / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) hKp
    have e : g₁ * (M.Kp + 1) = M.Kp * g₁ + g₁ := by ring
    have h3 : M.Kp * g₁ ≤ 1 := by linarith
    linarith
  refine ⟨fun βR hβ hmass hy => ?_, fun h4 b hU hmV hgb => ?_⟩
  · obtain ⟨hmR, hKz⟩ := hMK (hmass.trans hy)
    have hF' := hF N R hP hi0 hRℓ hRA hRρ (by omega) (N - 2) (by omega) m hmR hKz
    exact M.fa_bracket_all hgε hs R hP hi0 hRℓ hRA hRρ hN2 (by omega) hmR hF' hβ hmass
      (hy.trans hg₁3) (hCg _ (one_div_pos.2 hβ).le hy)
  · obtain ⟨hmR, hKz⟩ := hMK h4
    have hF' := hF N R hP hi0 hRℓ hRA hRρ (by omega) (N - 2) (by omega) m hmR hKz
    exact M.fa_locate hs R hP hi0 hRℓ hRA hRρ hN2 (by omega) hmR hF' hU hmV
      (hgb.trans (hg₁3.trans (by linarith))) (hgb.trans hg₁8) (hCg _ (hX0.trans hmV) hgb)

set_option maxHeartbeats 4000000 in
/-- **Theorem `thm:multiscale` (outline) at `h = 0` for the solutions of the shooting problem.**
Prefix as `thm_multiscale_final_h0`. Conclusion: a solution `b` (`H0Sol`) with the pair bound
exists; **every** `b` in the bracket `[bFin(1/(2β_R)), bFin(2/β_R)]` satisfies the pair bound
`|P_{1/b}[0 ↔ x] − ϑ_j²| ≤ Kϑ_j²/β_j` (`j ≤ j_x ≤ j + 1`, `j_x ≤ N − 2`); and every solution
`b` (`H0Sol`) with `b ∈ U_fix` and `m²L^{2N} ≤ ǧ^c_{N−2}(b) ≤ g₀` lies in that bracket (hence
satisfies the pair bound). -/
theorem thm_multiscale_final_h0_all : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ K : ℝ) (N₀ : ℕ), 0 < g₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
    (∃ b, H0Sol M R m βR b ∧
      ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ N - 2 →
        ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
          jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
          |Pconn L N (1 / b) x - thetaSq R m b (b - m) jp| ≤
            K * thetaSq R m b (b - m) jp / betaJ R m b (b - m) jp) ∧
    (∀ b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (1 / (2 * βR)))
        (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (2 / βR)),
      0 < b ∧ (∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
      ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ N - 2 →
        ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
          jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
          |Pconn L N (1 / b) x - thetaSq R m b (b - m) jp| ≤
            K * thetaSq R m b (b - m) jp / betaJ R m b (b - m) jp) ∧
    ∀ b, H0Sol M R m βR b →
      b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε →
      m * (L : ℝ) ^ (2 * N) ≤
        Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε b →
      Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε b ≤ g₀ →
      b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (1 / (2 * βR)))
        (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (2 / βR)) ∧
      ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ N - 2 →
        ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
          jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
          |Pconn L N (1 / b) x - thetaSq R m b (b - m) jp| ≤
            K * thetaSq R m b (b - m) jp / betaJ R m b (b - m) jp := by
  obtain ⟨L₀, h⟩ := fa_main
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, g₀, K, N₀, hg, hF⟩ := h L hL
  refine ⟨M, g₀, K, N₀, hg, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβ hmass hy
  obtain ⟨hA, hB⟩ := hF N R hP hi0 hRℓ hRA hRρ hN m hm
  obtain ⟨⟨b, hb, -, hby, hD, hPb⟩, hall⟩ := hA βR hβ hmass hy
  have e₂ : (2 : ℝ) / βR = 1 / (βR / 2) := by field_simp
  rw [e₂]
  refine ⟨⟨b, ⟨hb, hby, hD⟩, hPb⟩, hall, fun b hsol hU hmV hgb => ?_⟩
  obtain ⟨-, hby, -⟩ := hsol
  obtain ⟨-, -, hbr, -, hPb⟩ := hB (hmass.trans hy) b hU hmV hgb
  rw [hby] at hbr
  have e₁ : 1 / βR / 2 = 1 / (2 * βR) := by field_simp
  have e₃ : 2 * (1 / βR) = 1 / (βR / 2) := by field_simp
  rw [e₁, e₃] at hbr
  exact ⟨hbr, hPb⟩

set_option maxHeartbeats 4000000 in
/-- **Per-`b` form (for `cor:window`).** Constants as in `fa_main`. For `N ≥ N₀`, `m² > 0` and
every `b`, with `y := Re ǧ_N(b, b − m²)`: (i) if `0 < y`, `4m²L^{2N} ≤ y ≤ g₀` and
`b ∈ [bFin(y/2), bFin(2y)]` (`b` solves its own shooting problem inside its bracket), then the
`h = 0` trajectory is in `D_ε` and the pair bound holds at `b`; (ii) if `b ∈ U_fix` with
`4m²L^{2N} ≤ ǧ^c_{N−2}(b) ≤ g₀`, then `y ≥ 4ǧ^c/5 > 0`, `b ∈ [bFin(y/2), bFin(2y)]` and the pair
bound holds at `b`. -/
theorem thm_multiscale_h0_perb : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ K : ℝ) (N₀ : ℕ), 0 < g₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m b : ℝ, 0 < m →
      (0 < gFinH0 R (N - 2) m b → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ gFinH0 R (N - 2) m b →
        gFinH0 R (N - 2) m b ≤ g₀ →
        b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m
            (gFinH0 R (N - 2) m b / 2))
          (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (2 * gFinH0 R (N - 2) m b)) →
        0 < b ∧ (∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧ FwPairBd6 K R (N - 2) m b) ∧
      (b ∈ Ufix (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε →
        4 * (m * (L : ℝ) ^ (2 * N)) ≤
          Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε b →
        Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε b ≤ g₀ →
        4 / 5 * Hist.gN (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT (N - 2)
            M.core.ε b ≤ gFinH0 R (N - 2) m b ∧ 0 < gFinH0 R (N - 2) m b ∧
          b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m
              (gFinH0 R (N - 2) m b / 2))
            (bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (2 * gFinH0 R (N - 2) m b)) ∧
          FwPairBd6 K R (N - 2) m b) := by
  obtain ⟨L₀, h⟩ := fa_main
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, g₀, K, N₀, hg, hF⟩ := h L hL
  refine ⟨M, g₀, K, N₀, hg, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m b hm
  obtain ⟨hA, hB⟩ := hF N R hP hi0 hRℓ hRA hRρ hN m hm
  refine ⟨fun hy0 hmass hy hbr => ?_, fun hU h4 hgb => ?_⟩
  · set y := gFinH0 R (N - 2) m b with hyd
    have hβ : 0 < 1 / y := one_div_pos.2 hy0
    have e : 1 / (1 / y) = y := one_div_one_div y
    have e₁ : 1 / (2 * (1 / y)) = y / 2 := by field_simp
    have e₂ : 1 / (1 / y / 2) = 2 * y := by field_simp
    obtain ⟨-, hall⟩ := hA (1 / y) hβ (by rw [e]; exact hmass) (by rw [e]; exact hy)
    rw [e₁, e₂] at hall
    exact hall b hbr
  · have hX0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.le (by positivity)
    obtain ⟨k1, k2, k3, -, k5⟩ := hB (h4.trans hgb) b hU (by linarith) hgb
    exact ⟨k1, k2, k3, k5⟩

end

end Spin2
