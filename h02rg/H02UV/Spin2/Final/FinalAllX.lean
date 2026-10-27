import Spin2.Final.FinalTop
import Spin2.Cont.ContTheta

/-!
# `thm:multiscale` at `h = 0` for every `b` in the bracket and every `x ≠ 0` (A0')

`Spin2/Final/FinalAll` (`fa_main`) and `Spin2/Cont/ContTheta` (`ct_main`) give, for every `b` in the bracket
`[bFin(1/(2β_R)), bFin(2/β_R)]`, the pair bound for `x ≠ 0` with `j_x ≤ N − 2`. Here the same is
done with the result predicate `FwResT = FwRes6 ∧ FwTopBd` of `Spin2/Final/FinalTop` (chain
`fb_constsT`), so that the bound holds for **all** `x ≠ 0` at the scale `min(j_p, N − 2)`:

* **`FwAllBd K`**: for all `x ≠ 0`, `j_p = jPhys(|x|/L^N)`, `j_p ≤ j_x ≤ j_p + 1` and
  `|P_{1/b}[0 ↔ x] − ϑ_k²| ≤ Kϑ_k²/β_k`, `k = min(j_p, N_h)`.
* **`fwAll_of`**: `FwPairBd6 K ∧ FwTopBd K'` (and `D_ε`) give `FwAllBd (max K K')`.
* **`MasterFacts.ct_bracket_gT`**: `ct_bracket_g` with `FwResT`.
* **`thm_multiscale_final_h0_allB`**: `ct_main` with `FwAllBd` (and the existence of a shooting
  solution in the bracket).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

/-- **The pair bound for all `x ≠ 0`** at the scale `min(j_p, N_h)`. -/
def FwAllBd {L : ℕ} [NeZero L] (K : ℝ) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (Nh : ℕ) (m b : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 →
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pconn L N (1 / b) x - thetaSq R m b (b - m) (min jp Nh)| ≤
        K * thetaSq R m b (b - m) (min jp Nh) / betaJ R m b (b - m) (min jp Nh)

/-- **`FwPairBd6 K ∧ FwTopBd K'` give `FwAllBd (max K K')`** (along a `D_ε` trajectory). -/
theorem fwAll_of {L : ℕ} [NeZero L] (hL : 2 ≤ L) {κ cm cT ε K K' : ℝ} {N : ℕ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} {m b : ℝ} (hb : 0 < b)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (hP1 : FwPairBd6 K R Nh m b) (hP2 : FwTopBd K' R Nh m b) :
    FwAllBd (max K K') R Nh m b := by
  intro x hx
  have hnn : ∀ k ≤ Nh, 0 ≤ thetaSq R m b (b - m) k / betaJ R m b (b - m) k := fun k hk => by
    have hg := (hD k hk).1
    unfold thetaSq betaJ
    exact div_nonneg (Real.rpow_nonneg (div_nonneg (one_div_pos.2 hg).le
      (one_div_pos.2 hb).le) _) (one_div_pos.2 hg).le
  rcases Nat.lt_or_ge Nh (Obs.coal L (0 : Lam 2 L N) x) with hc | hc
  · obtain ⟨jp, h1, h2, h3⟩ := coal_jPhys hL hx
    refine ⟨jp, h1, h2, h3, ?_⟩
    have hmin : min jp Nh = Nh := by
      rcases Nat.lt_or_ge jp Nh with hj | hj
      · -- `jp < Nh < j_x ≤ jp + 1` is impossible
        omega
      · exact min_eq_right hj
    rw [hmin]
    refine (hP2 x hx hc).trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (hnn Nh le_rfl)
  · obtain ⟨jp, h1, h2, h3, h4⟩ := hP1 x hx hc
    refine ⟨jp, h1, h2, h3, ?_⟩
    rw [min_eq_left (h2.trans hc)]
    refine h4.trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn jp (h2.trans hc))

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

set_option maxHeartbeats 4000000 in
/-- **`ct_bracket_g` with `FwResT`** (the top bound `FwTopBd` added). Original: the bracket with a lower bound on `ǧ^0_{N_h}` (`fa_bracket_all`, second part, plus
`ǧ^0_{N_h}(b) ≥ (7/8)ǧ^c_{N_h}(b) ≥ 7/(32β_R)`). -/
theorem ct_bracket_gT {pW g₀ K K' : ℝ} (hgε : g₀ ≤ M.core.ε / 2)
    (hs : pW * cmu ((L : ℝ) ^ 2) M.core.cm ≤ 1 / 12) {N : ℕ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N)
    {m : ℝ} (hm : m ∈ mRange L N)
    (hF' : ∀ b μc : ℝ, 0 < b →
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μc →
      m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ≤ g₀ → FwResT M pW K K' R Nh m b μc)
    {βR : ℝ} (hβ : 0 < βR) (hmass : 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR)
    (hyg : 1 / βR ≤ g₀ / 3) (hcy : 100 * M.core.Cb * (1 / βR) ≤ 1) :
    ∀ b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (2 * βR)))
        (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (βR / 2))),
      0 < b ∧ (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧ FwPairBd6 K R Nh m b ∧
      FwTopBd K' R Nh m b ∧ 1 / βR / 5 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
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
  set g₁ := (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁ Nh).1 with hg₁d
  set g₂ := (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1 with hg₂d
  have N₁' : |g₁ - 1 / βR / 2| ≤ 4 * M.core.Cb * (1 / βR / 2) ^ 2 := N₁
  have N₂' : |g₂ - 2 * (1 / βR)| ≤ 4 * M.core.Cb * (2 * (1 / βR)) ^ 2 := N₂
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
  intro b hb
  obtain ⟨ham, hl, hu⟩ := hBe b hb
  have hgc0 : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b
      (Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b) Nh).1 :=
    (ham.1 Nh le_rfl).1.le
  obtain ⟨hD, hd, hPb, hTb⟩ := hF' b _ (hb₁.trans_le hb.1) ham (hm₁.trans hl) (hu.trans hg₂g)
  have hs' := fb_s_le hs hgc0
  have hd' := (abs_le.1 hd).1
  refine ⟨hb₁.trans_le hb.1, hD, hPb, hTb, ?_⟩
  linarith

end MasterFacts

set_option maxHeartbeats 4000000 in
/-- **Theorem `thm:multiscale` (outline) at `h = 0` for every `b` in the bracket and every
`x ≠ 0`** (constants `M, g₀, K, N₀` depending on `L` only). For `N ≥ N₀`, `m² > 0`,
`4m²L^{2N} ≤ 1/β_R ≤ g₀`: `m² ∈ mRange`; a shooting solution (`H0Sol`) exists in the bracket
`[bFin(1/(2β_R)), bFin(2/β_R)]`; every `b` in the bracket has `b > 0`, the `h = 0` trajectory in
`D_ε` up to `N − 2`, the pair bound **for all `x ≠ 0`** at the scale `min(j_p, N − 2)`
(`FwAllBd K`) and `ǧ^0_{N−2}(b) ≥ 1/(5β_R)`; every `H0Sol` with `b ∈ U_fix` and
`m²L^{2N} ≤ ǧ^c_{N−2}(b) ≤ g₀` lies in the bracket. -/
theorem thm_multiscale_final_h0_allB : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ K : ℝ) (N₀ : ℕ), 0 < g₀ ∧ g₀ ≤ 1 ∧ 3 ≤ N₀ ∧
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
  obtain ⟨L₀, h⟩ := fb_constsT
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, pW, g₀, K, K', hg, hgε, hs, hF⟩ := h L hL
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
  refine ⟨M, g₁, max K K', 4 + ⌈4 * M.Kp⌉₊, hg₁0, hg₁1, by omega, ?_⟩
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
