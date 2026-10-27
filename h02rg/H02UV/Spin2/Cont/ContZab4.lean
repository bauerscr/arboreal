import Spin2.Cont.ContZab3

set_option autoImplicit false

/-!
# B3, T6, route (c): `Z_{ab}` in the fixed weight; the explicit `Q`

Fixed weight `w = wM(k2Ma … J, pM(ptsS y)_{N_h})` (that of `k2_mid`, `k2_top`).

* the ratios: `pM(P)_{ms}/k2Ma ≤ (7/5)^{J−ms}|β^P_{ms}|/M₀` (`k2_envRatio`) and
  `pM(ptsS y)_{ms}/pM(ptsS y)_{N_h} ≤ Θ_b(ms)` (`cw2_pMS_ratio`);
* `zabZr = (7/5)^{J−ms}Θ_b(ms)/M₀·(|β^{(y−x,y)}_{ms}|(c_{ab}r_{ms}(2c_W)² + 4|y−x|_∞L^{−ms}ι_ZA) +
  |β^{(0,y)}_{ms}|c_{ab}r_{ms}(2c_W)²)`;
* **`MasterFacts.zab_Zfix`**: the input `hZ` of `k2_mid`/`k2_top` holds with `Z_{ab} = zabZr`
  (`ms < N_h`, `ms ≤ J ≤ N_h`, `δ.IsObs`, `0 < M₀`; no other input);
* `zabQ Q₀ = Q₀ + √(zabZr/(c_{ab}r_{ms}))`; **`zabQ_spec`**: for `c_{ab} > 0` it satisfies `hQz`,
  and dominates `Q₀` (so `hQw`, `hQk` for `Q₀` give them for `zabQ Q₀`).
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 ENNReal Step2.D2

variable {L : ℕ} [NeZero L]

/-- **`Z_{ab}` in ratio form** (fixed weight `wM(k2Ma … J, pM(ptsS y)_{N_h})`). -/
def zabZr (M : MasterFacts L) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (m b μ₀ : ℝ) (x y : Lam 2 L N) (ms : ℕ) (M₀ : ℝ) (J Nh : ℕ) : ℝ :=
  (7 / 5) ^ (J - ms) * cw2Thb M Nh ms / M₀ *
    (‖bt2 R (pl2Pts x y) (zV0 b) m b μ₀ ms‖ *
        (M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) *
          (2 * M.core.cWo) ^ 2 +
          4 * supNorm (y - x) / (L : ℝ) ^ ms * zabIota M.core.cWo * M.core.A) +
      ‖bt2 R (ptsX y) (zV0 b) m b μ₀ ms‖ *
        (M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) *
          (2 * M.core.cWo) ^ 2))

/-- **The explicit `Q`**: `Q₀ + √(Z_{ab}/(c_{ab}r_{ms}))`. -/
def zabQ (M : MasterFacts L) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (m b μ₀ : ℝ) (x y : Lam 2 L N) (ms : ℕ) (M₀ : ℝ) (J Nh : ℕ) (Q₀ : ℝ) : ℝ :=
  Q₀ + Real.sqrt (zabZr M R m b μ₀ x y ms M₀ J Nh /
    (M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1)))

/-- **`zabQ` dominates `Q₀` and satisfies `Z_{ab} ≤ c_{ab}r_{ms}Q²`** (`c_{ab}r_{ms} > 0`). -/
theorem zabQ_spec (M : MasterFacts L) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (m b μ₀ : ℝ) (x y : Lam 2 L N) (ms : ℕ) (M₀ : ℝ) (J Nh : ℕ) {Q₀ : ℝ}
    (hQ0 : 0 ≤ Q₀)
    (hr : 0 < M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1)) :
    Q₀ ≤ zabQ M R m b μ₀ x y ms M₀ J Nh Q₀ ∧ 0 ≤ zabQ M R m b μ₀ x y ms M₀ J Nh Q₀ ∧
    zabZr M R m b μ₀ x y ms M₀ J Nh ≤
      M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) *
        zabQ M R m b μ₀ x y ms M₀ J Nh Q₀ ^ 2 := by
  set c := M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1) with hc
  set Z := zabZr M R m b μ₀ x y ms M₀ J Nh with hZ
  have hs0 := Real.sqrt_nonneg (Z / c)
  have h1 : Q₀ ≤ Q₀ + Real.sqrt (Z / c) := le_add_of_nonneg_right hs0
  refine ⟨h1, hQ0.trans h1, ?_⟩
  have h2 : Z / c ≤ Real.sqrt (Z / c) ^ 2 := by
    rcases le_total 0 (Z / c) with h | h
    · rw [Real.sq_sqrt h]
    · exact h.trans (sq_nonneg _)
  have h3 : Real.sqrt (Z / c) ^ 2 ≤ (Q₀ + Real.sqrt (Z / c)) ^ 2 :=
    pow_le_pow_left₀ hs0 (le_add_of_nonneg_left hQ0) 2
  have h4 : Z = c * (Z / c) := by field_simp
  show Z ≤ c * (Q₀ + Real.sqrt (Z / c)) ^ 2
  rw [h4]
  exact mul_le_mul_of_nonneg_left (h2.trans (by rwa [← h4])) hr.le

namespace MasterFacts

variable (M : MasterFacts L)

set_option maxHeartbeats 8000000 in
/-- **The ratio form of `zabZ` in the fixed weight.** -/
theorem zab_Z_le (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x y : Lam 2 L N) {ms J : ℕ} (hmsJ : ms ≤ J) (hJ : J ≤ Nh) (δ : ObsSt .two L N)
    (hδ : δ.IsObs) {M₀ : ℝ} (hM0 : 0 < M₀)
    (hMa : 0 < k2Ma R m b μ₀ y ms δ M₀ J) :
    zabZ M R m b μ₀ x y ms (k2Ma R m b μ₀ y ms δ M₀ J)
        (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh) ≤
      zabZr M R m b μ₀ x y ms M₀ J Nh := by
  have hN2 : 2 ≤ N := by omega
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb0
  have hNh0 : 0 < Nh := by
    omega
  have henv := M.core.k2_envRatio N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX y) (zV0 b)
    ms δ hδ hM0.le (i := 0) (i' := J - ms) (Nat.zero_le _) (by omega)
  simp only [add_zero, rkEnv_zero, Nat.sub_zero, Nat.add_sub_cancel' hmsJ] at henv
  have henv' : 2 * histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀ ≤
      (7 / 5) ^ (J - ms) * k2Ma R m b μ₀ y ms δ M₀ J := henv
  have hrat := M.cw2_pMS_ratio N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD y
    (j := ms) (by omega)
  have hβS := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsS y)
    (zV0 b) rfl hmu hNh0 Nh le_rfl).1
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, -⟩ := id M.core.hC2
  have hρ0' : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have hsN := histS_pos' (R.withMsq m) hρ0' hρ8' t Nh
  have hsm := histS_pos' (R.withMsq m) hρ0' hρ8' t ms
  set Ma := k2Ma R m b μ₀ y ms δ M₀ J with hMad
  set Mb := pM (R.withMsq m) (ptsS y) (zV0 b) t Nh with hMbd
  have hMb : 0 < Mb := by
    show 0 < 2 * histS (R.withMsq m) Nh t ^ 2 * _; positivity
  set Θ := cw2Thb M Nh ms with hΘ
  have hΘ0 : 0 < Θ := cw2Thb_pos M Nh ms
  set q := (7 / 5 : ℝ) ^ (J - ms) with hq
  have hq0 : 0 < q := by positivity
  -- the two `a`-ratios and the `b`-ratio
  have hra : ∀ B : ℝ, 0 ≤ B →
      2 * histS (R.withMsq m) ms t ^ 2 * B / Ma ≤ q * B / M₀ := by
    intro B hB
    rw [div_le_div_iff₀ hMa hM0]
    have := mul_le_mul_of_nonneg_left henv' hB
    calc 2 * histS (R.withMsq m) ms t ^ 2 * B * M₀ =
        B * (2 * histS (R.withMsq m) ms t ^ 2 * M₀) := by ring
      _ ≤ B * (q * Ma) := this
      _ = q * B * Ma := by ring
  have hrb : pM (R.withMsq m) (ptsS y) (zV0 b) t ms / Mb ≤ Θ := by
    rw [div_le_iff₀ hMb]
    refine hrat.trans (le_of_eq ?_)
    rw [hΘ]; unfold cw2Thb; rfl
  set Z1 := M.k2cab * (M.core.c * (t ms).1) * (2 * M.core.cWo) ^ 2 with hZ1
  set E := 4 * (supNorm (y - x) : ℝ) / (L : ℝ) ^ ms * zabIota M.core.cWo * M.core.A with hE
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc2 : 0 ≤ M.core.c := by
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
      rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
    have := hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
    linarith
  have hZ10 : 0 ≤ Z1 := mul_nonneg (mul_nonneg M.k2cab_nonneg
    (mul_nonneg hc2 (hD ms (by omega)).1.le)) (sq_nonneg _)
  have hE0 : 0 ≤ E := by
    have hA2 : 2 ≤ M.core.A := M.core.hA2
    have hcW : 1 ≤ M.core.cWo := M.core.consts_nonneg.2.2.2.2.2.1
    have : 0 ≤ zabIota M.core.cWo := mul_nonneg (Real.exp_pos _).le (by linarith)
    exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (pow_pos hL0 _).le) this) (by linarith)
  set β1 := ‖bt2 R (pl2Pts x y) (zV0 b) m b μ₀ ms‖ with hβ1
  set β2 := ‖bt2 R (ptsX y) (zV0 b) m b μ₀ ms‖ with hβ2
  set sS := pM (R.withMsq m) (ptsS y) (zV0 b) t ms with hsS
  have hsS0 : 0 ≤ sS := by
    show 0 ≤ 2 * histS (R.withMsq m) ms t ^ 2 * _; positivity
  have hp1 : pM (R.withMsq m) (pl2Pts x y) (zV0 b) t ms = 2 * histS (R.withMsq m) ms t ^ 2 * β1 := rfl
  have hp2 : pM (R.withMsq m) (ptsX y) (zV0 b) t ms = 2 * histS (R.withMsq m) ms t ^ 2 * β2 := rfl
  have key : ∀ B : ℝ, 0 ≤ B → 2 * histS (R.withMsq m) ms t ^ 2 * B * sS / (Ma * Mb) ≤
      q * Θ / M₀ * B := by
    intro B hB
    have h1 := hra B hB
    have e : 2 * histS (R.withMsq m) ms t ^ 2 * B * sS / (Ma * Mb) =
        (2 * histS (R.withMsq m) ms t ^ 2 * B / Ma) * (sS / Mb) := by
      field_simp
    rw [e]
    calc 2 * histS (R.withMsq m) ms t ^ 2 * B / Ma * (sS / Mb) ≤ q * B / M₀ * Θ :=
          mul_le_mul h1 hrb (div_nonneg hsS0 hMb.le) (div_nonneg (mul_nonneg hq0.le hB) hM0.le)
      _ = q * Θ / M₀ * B := by ring
  show pM (R.withMsq m) (pl2Pts x y) (zV0 b) t ms * sS / (Ma * Mb) * (Z1 + E) +
      pM (R.withMsq m) (ptsX y) (zV0 b) t ms * sS / (Ma * Mb) * Z1 ≤
    q * Θ / M₀ * (β1 * (Z1 + E) + β2 * Z1)
  rw [hp1, hp2]
  have k1 := mul_le_mul_of_nonneg_right (key β1 (norm_nonneg _)) (add_nonneg hZ10 hE0)
  have k2 := mul_le_mul_of_nonneg_right (key β2 (norm_nonneg _)) hZ10
  nlinarith

set_option maxHeartbeats 8000000 in
/-- **`hZ` of `k2_mid`/`k2_top` discharged**: in the fixed weight
`wM(k2Ma … J, pM(ptsS y)_{N_h})`, `A^{(|𝓑(X)|−4)_+}w_{ab}T(δ.K(X)_{ab}) ≤ zabZr` for
`δ = pl2Delta` at `ms`. -/
theorem zab_Zfix (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ)
    (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x y : Lam 2 L N) {ms J : ℕ} (hms0 : 0 < ms) (hms : ms < Nh) (hmsJ : ms ≤ J) (hJ : J ≤ Nh)
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x) (hmy : ms < Obs.coal L (0 : Lam 2 L N) y)
    (hδ : (pl2Delta R m b μ₀ x y ms).IsObs) {M₀ : ℝ} (hM0 : 0 < M₀) :
    ∀ X, IsConn ms X → ENNReal.ofReal ((R.withMsq m).A ^ (nb ms X - 2 ^ 2)) *
      ((wM (k2Ma R m b μ₀ y ms (pl2Delta R m b μ₀ x y ms) M₀ J)
          (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)).ab *
        Tj 2 (L : ℝ) ms (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((pl2Delta R m b μ₀ x y ms).K X : SA .two (Lam 2 L N)).ab) ≤
      ENNReal.ofReal (zabZr M R m b μ₀ x y ms M₀ J Nh) := by
  intro X hX
  have hN2 : 2 ≤ N := by omega
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb0
  have hβS := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsS y)
    (zV0 b) rfl hmu (by omega) Nh le_rfl).1
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, -⟩ := id M.core.hC2
  have hρ0' : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8
  have hsN := histS_pos' (R.withMsq m) hρ0' hρ8' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh
  have hMb : 0 < pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh := by
    show 0 < 2 * histS (R.withMsq m) Nh _ ^ 2 * _; positivity
  by_cases hMa : 0 < k2Ma R m b μ₀ y ms (pl2Delta R m b μ₀ x y ms) M₀ J
  · exact (M.zab_Z N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b μ₀ hD x y hms0 hms hmx hmy hMa hMb
      X hX).trans (ENNReal.ofReal_le_ofReal (M.zab_Z_le N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm
        b μ₀ hD x y hmsJ hJ _ hδ hM0 hMa))
  · replace hMa := le_of_not_gt hMa
    have h0 : (wM (k2Ma R m b μ₀ y ms (pl2Delta R m b μ₀ x y ms) M₀ J)
        (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh)).ab = 0 := by
      show ENNReal.ofReal _ * _ = 0
      rw [ENNReal.ofReal_eq_zero.2 (inv_nonpos.2 hMa), zero_mul]
    rw [h0, zero_mul, mul_zero]
    exact zero_le

end MasterFacts

end

end Spin2
