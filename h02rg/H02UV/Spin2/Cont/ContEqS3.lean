import Spin2.Cont.ContEqS1

set_option autoImplicit false

/-!
# B3, `r`-dependent form: `ǧ_j ≤ 4/β_R` on the bracket

* `MasterFacts.eqs_bracket_up`: `ct_bracket_gT` (upper side) — on the bracket
  `[bFin(1/(2β_R)), bFin(2/β_R)]`, `ǧ_{N_h}(b, b − m²) ≤ (27/8)/β_R`.
* **`eqs_bracketUp`** (per `M`, constants of `eqs_constsT`): for `N ≥ N₀`, `4m²L^{2N} ≤ 1/β_R ≤ g₀`
  and `b` in `ctBracket`: `ǧ_j(b, b − m²) ≤ 4/β_R` for all `j ≤ N − 2` (monotonicity `gmonoD`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

set_option maxHeartbeats 4000000 in
/-- **The upper side of `ct_bracket_gT`**: `ǧ_{N_h}(b, b − m²) ≤ (27/8)/β_R` on the bracket. -/
theorem eqs_bracket_up {pW g₀ K K' : ℝ} (hgε : g₀ ≤ M.core.ε / 2)
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
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 27 / 8 * (1 / βR) := by
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
  obtain ⟨-, hd, -, -⟩ := hF' b _ (hb₁.trans_le hb.1) ham (hm₁.trans hl) (hu.trans hg₂g)
  have hs' := fb_s_le hs hgc0
  have hd' := (abs_le.1 hd).2
  linarith

end MasterFacts

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 4000000 in
/-- **`ǧ_j ≤ 4/β_R` on the bracket** (per `M`; constants as in `eqs_allB`). -/
theorem eqs_bracketUp (M : MasterFacts L) : ∃ (g₀ : ℝ) (N₀ : ℕ), 0 < g₀ ∧ 3 ≤ N₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
    ∀ b ∈ ctBracket M R m βR, ∀ j ≤ N - 2,
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 4 * (1 / βR) := by
  obtain ⟨pW, g₀, K, K', hg, hgε, hs, hF⟩ := eqs_constsT M
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
  obtain ⟨-, -, -, hε, -, -, -, -, -, -, -, hCb, -⟩ := M.core.hC2
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  set g₁ := min (g₀ / 3) (min (1 / (100 * (M.core.Cb + 1))) (min (1 / (M.Kp + 1)) 1)) with hg₁d
  have hg₁3 : g₁ ≤ g₀ / 3 := min_le_left _ _
  have hg₁C : g₁ ≤ 1 / (100 * (M.core.Cb + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hg₁K : g₁ ≤ 1 / (M.Kp + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hg₁1 : g₁ ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCg : ∀ y, 0 ≤ y → y ≤ g₁ → 100 * M.core.Cb * y ≤ 1 := fun y hy0 hy => by
    have h1 : y * (100 * (M.core.Cb + 1)) ≤ 1 := by
      have := hy.trans hg₁C
      rwa [le_div_iff₀ (by positivity)] at this
    have e : y * (100 * (M.core.Cb + 1)) = 100 * M.core.Cb * y + 100 * y := by ring
    linarith
  have hg₁0 : 0 < g₁ := lt_min (by linarith) (lt_min (by positivity) (lt_min (by positivity)
      one_pos))
  refine ⟨g₁, 4 + ⌈4 * M.Kp⌉₊, hg₁0, by omega, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβ hmass hy b hb j hj
  have hN2 : 2 ≤ N := by omega
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
  have e₂ : (2 : ℝ) / βR = 1 / (βR / 2) := by field_simp
  rw [ctBracket, e₂] at hb
  have hup := M.eqs_bracket_up hgε hs R hP hi0 hRℓ hRA hRρ hN2 (by omega) hmR hFT hβ hmass
    (hy.trans hg₁3) (hCg _ (one_div_pos.2 hβ).le hy) b hb
  obtain ⟨-, hD, -, -, -⟩ := M.ct_bracket_gT hgε hs R hP hi0 hRℓ hRA hRρ hN2 (by omega)
    hmR hFT hβ hmass (hy.trans hg₁3) (hCg _ (one_div_pos.2 hβ).le hy) b hb
  have hmono := M.gmonoD N R hP hi0 hRℓ hRA hRρ hN2 (N - 2) (by omega) m hmR b (b - m) hD
  have key : ∀ n, j + n ≤ N - 2 → (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (j + n)).1 := by
    intro n
    induction n with
    | zero => intro _; exact le_rfl
    | succ n ih => intro hn; exact (ih (by omega)).trans (hmono (j + n) (by omega))
  have := key (N - 2 - j) (by omega)
  rw [show j + (N - 2 - j) = N - 2 by omega] at this
  have hy0 : 0 < 1 / βR := one_div_pos.2 hβ
  linarith

end

end Spin2
