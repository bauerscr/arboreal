import Spin2.Pair.PairZeroAB1
import Spin2.Pair.PairDef6b

/-!
# `PairZeroRemAB` and the last-step defect from the `ab` sizes at `N_h + 1`

* **`PairTopSizesAB c_V c_W c_K`**: the `ab` sizes of the reduced history at `N_h + 1` in the
  weights `wM(M_{a,N_h}, M_b)` (`‖V'_{N_h+1}(B)‖ ≤ c_V`, `‖𝒲'_{N_h+1}(B)‖ ≤ c_Wǧ_{N_h}`,
  `A^{(|𝓑(X)|-4)_+}‖K'_{N_h+1}(X)‖ ≤ c_K`): one step of the `ab` chain past `N_h`.
* **`pairZeroAB_of`** (trajectory level, all `x`): from `PairTopSizesAB`, `PairRRelR c_r`, `P₀ = 1`,
  `Case2TopStep`, the weight bound `M_{a,N_h} ≤ c_u‖M_{j_x}‖ǧ_{N_h}`, the jet bound
  `LastJetBd L (A/2) r₀` and the smallness of the last step:
  **`PairZeroRemAB e₁ 1`** with `e₁ = (81/16)c_{Jab}c_S + c_r` and **`PairDefLastR c_L`** with
  `c_L = c_{Lab}c_Sc_u`, `c_S = c_V + c_W + 8c_K + 1`; item (d) uses the zero-mode constant
  `|zCc| ≥ 1/(2m|Z_N|L^{2N})` and the mass window `2·(81/16)c_J(c_ρ + 4/r₀²)c_Sℓ²·mL^{2N} ≤ 1`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The `ab` sizes of the reduced history at `N_h + 1`** (one step of the `ab` chain past the
horizon), in the weights `wM(M_{a,N_h}, M_b)`. -/
def PairTopSizesAB (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (cV cW cK : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    (∀ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM (vwA R m b μ₀ x Nh) (vwB R m b μ₀ lam x)) (Nh + 1)
        (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b') ≤ ENNReal.ofReal cV) ∧
    (∀ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM (vwA R m b μ₀ x Nh) (vwB R m b μ₀ lam x)) (Nh + 1)
        (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W b') ≤
        ENNReal.ofReal (cW * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)) ∧
    (∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Obs2.oTo (wM (vwA R m b μ₀ x Nh) (vwB R m b μ₀ lam x)) (Nh + 1)
        (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X) ≤ ENNReal.ofReal cK)

set_option maxHeartbeats 8000000 in
/-- **`PairZeroRemAB` and `PairDefLastR` from the `ab` sizes at `N_h + 1`** (trajectory level). -/
theorem pairZeroAB_of {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Cf cW cK r₀ : ℝ} (hm0 : 0 < m)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) (hLp : pauliL0 2 ≤ L)
    (hL8 : 2 ^ (2 + 3) + 8 * 2 < L) (hA2 : 2 ≤ R.A)
    (hmN : |(R.withMsq m).msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1)
    (hG : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (R.A / 2) r₀)
    (hcW : 0 ≤ cW) (hcK : 0 ≤ cK) (hCf : 0 ≤ Cf)
    (hg0 : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1)
    (hs1 : 2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ R.ρ)
    (hs2 : 8 * cM * R.ℓ ^ 2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 / 2)
    (hs3 : cRho L * (cTauL R.ℓ Cf cW cK * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1)
    (hs4 : 4 * (cTauL R.ℓ Cf cW cK * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ r₀ ^ 2)
    (hs5 : cTauL R.ℓ Cf cW cK * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ r₀)
    (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (hRd : PairSectRed R Nh m b μ₀ oR)
    {cVo cWo cKo : ℝ} (hcVo : 0 ≤ cVo) (hcWo : 0 ≤ cWo) (hcKo : 0 ≤ cKo)
    (hTop : PairTopSizesAB R Nh m b μ₀ lam oR cVo cWo cKo)
    (htop : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → Case2TopStep R (ptsX x) (zV b) Nh m b μ₀)
    (hβne : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → hBeta R m b μ₀ x Nh ≠ 0)
    (hMb : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → 0 < vwB R m b μ₀ lam x)
    {cu : ℝ} (hcu : 0 ≤ cu)
    (hvwA : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      vwA R m b μ₀ x Nh ≤ cu * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    {cr : ℝ} (hRR : PairRRelR R Nh m b μ₀ lam oR cr)
    (hP1 : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → zP0 R Nh m b μ₀ x = 1)
    {Kt : ℝ}
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (cVo + cWo + 8 * cKo + 1) *
      R.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) :
    PairZeroRemAB R Nh m b μ₀ lam oR (81 / 16 * cJab L r₀ * (cVo + cWo + 8 * cKo + 1) + cr) 1 ∧
    PairDefLastR R Nh m b μ₀ lam oR (cLab L * (cVo + cWo + 8 * cKo + 1) * cu) := by
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ1 : (R.withMsq m).ρ < 1 := by linarith [hVL.2.2.2.2.2.1]
  set cS := cVo + cWo + 8 * cKo + 1 with hcSd
  have hcS : 1 ≤ cS := by rw [hcSd]; linarith
  -- the per-`x` bounds
  have hxB : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ∃ s' : ℝ, 0 < s' ∧
      histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 ≤ (9 / 8) ^ 2 * s' ^ 2 ∧
      histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 ≤
        (9 / 8) ^ 2 * R.ℓ ^ 2 /
          ‖(lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ ∧
      s' ^ 2 * ‖Suscept.c2 (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
        cJab L r₀ * cS * (vwA R m b μ₀ x Nh * vwB R m b μ₀ lam x) ∧
      ‖ε (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
        cJet L * (cRho L + 4 / r₀ ^ 2) * cS * (vwA R m b μ₀ x Nh * vwB R m b μ₀ lam x) ∧
      ‖lastDefR R Nh m b μ₀ oR x‖ ≤ cLab L * cS * (vwA R m b μ₀ x Nh * vwB R m b μ₀ lam x) := by
    intro x hx h1 hj
    obtain ⟨hobs, hloc0, hab0, -⟩ := hRd x hx h1 hj
    obtain ⟨hVo, hWo, hKo⟩ := hTop x hx h1 hj
    have hMa : 0 < vwA R m b μ₀ x Nh := by
      unfold vwA; rw [if_neg (hβne x hx h1 hj)]
      have := histS_pos' (R.withMsq m) hρ0 hVL.2.2.2.2.2.1 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh
      have := norm_pos_iff.2 (hβne x hx h1 hj)
      positivity
    exact pairLastAB_x R hNh hV hVL hVN hLp hL8 hA2 hmN hG hr₀ hr₀1 hJ hcW hcK hCf hg0 hg1 hs1 hs2
      hs3 hs4 hs5 oR x hj hobs hloc0 hab0 hMa (hMb x hx h1 hj) hcVo hcWo hcKo hVo hWo hKo
  -- the couplings
  have hβ : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      ‖hBeta R m b μ₀ x Nh‖ ≤ 2 * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ := by
    intro x hx h1 hj
    set P := ptsX (L := L) (N := N) x
    have hflow := bt2_flow R P (zV b) (Nh := Nh + 1) (by omega) m b μ₀ (k := Nh) (by omega)
    have hBB : ‖bt2 R P (zV b) m b μ₀ Nh‖ ≤ 2 * ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ := by
      rw [hflow]; exact beta_step_ge (htop x hx h1 hj).1 (htop x hx h1 hj).2
    have hβeq : ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ₀ x)‖ =
        ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ := by
      have h : Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ₀ x) =
          Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (Obs2.histVO2 (R.withMsq m) P
            (Obs2.obsInit .two (zV b) P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)) := by
        unfold Obs2.betaTot2
        refine sum_congr rfl fun b' _ => ?_
        rw [Obs2.histVO2_a]
        congr 1
        exact Obs2.emb_add_cmp true _ _
      rw [h]; rfl
    rw [hβeq]; exact hBB
  have hvwAeq : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      vwA R m b μ₀ x Nh = 2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖hBeta R m b μ₀ x Nh‖ := fun x hx h1 hj => by
    unfold vwA; rw [if_neg (hβne x hx h1 hj)]
  refine ⟨fun x hx h1 hj => ?_, fun x hx h1 hj => ?_⟩
  · obtain ⟨s', hs', hsc1, hsc2, hc2, hε, -⟩ := hxB x hx h1 hj
    have hP := hP1 x hx h1 hj
    refine ⟨?_, ?_⟩
    · simp only [hP, norm_one, mul_one]
      set β1 := ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ with hβ1
      set Mj := ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ with hMj
      set gj := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 with hgj
      set sN := histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) with hsN
      have hvB : vwB R m b μ₀ lam x = Mj * gj := rfl
      have hβx := hβ x hx h1 hj
      have hvA := hvwAeq x hx h1 hj
      have hβ10 : 0 ≤ β1 := norm_nonneg _
      have hVB0 : 0 ≤ Mj * gj := (hMb x hx h1 hj).le
      have hcJ0 : 0 ≤ cJab L r₀ := by
        unfold cJab
        have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
        have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
        have hcS' : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
        have h1 : 0 ≤ cJet L := by
          unfold cJet; have := mul_nonneg hL2 (by linarith : (0 : ℝ) ≤ Q1 2); linarith
        have h2 : 0 ≤ cRho L := by
          unfold cRho
          have : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
          have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
          refine mul_nonneg hL2 ?_
          nlinarith
        have := mul_nonneg h1 (add_nonneg h2 (by positivity : (0 : ℝ) ≤ 4 / r₀ ^ 2))
        positivity
      -- `|c2| ≤ (81/16) c_{Jab} c_S ‖M‖ǧ β₁`
      have hc2' : ‖Suscept.c2 (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
          81 / 16 * cJab L r₀ * cS * (Mj * gj * β1) := by
        have hs2 : 0 < s' ^ 2 := by positivity
        have k1 : vwA R m b μ₀ x Nh * vwB R m b μ₀ lam x ≤ 2 * ((9 / 8) ^ 2 * s' ^ 2) *
            (2 * β1) * (Mj * gj) := by
          rw [hvA, hvB]
          have := mul_le_mul hsc1 hβx (norm_nonneg _) (by positivity)
          have := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2)
          have := mul_le_mul_of_nonneg_right this hVB0
          nlinarith
        have k2 : s' ^ 2 * ‖Suscept.c2 (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
            s' ^ 2 * (81 / 16 * cJab L r₀ * cS * (Mj * gj * β1)) := by
          refine hc2.trans ?_
          have := mul_le_mul_of_nonneg_left k1 (mul_nonneg hcJ0 (by linarith : (0 : ℝ) ≤ cS))
          calc cJab L r₀ * cS * (vwA R m b μ₀ x Nh * vwB R m b μ₀ lam x)
              ≤ cJab L r₀ * cS * (2 * ((9 / 8) ^ 2 * s' ^ 2) * (2 * β1) * (Mj * gj)) := this
            _ = _ := by ring
        exact le_of_mul_le_mul_left k2 hs2
      have hrN := (hRR x hx h1 hj).2
      calc ‖Suscept.c2 (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab -
            rRN R Nh m b μ₀ oR x‖
          ≤ ‖Suscept.c2 (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab‖ +
            ‖rRN R Nh m b μ₀ oR x‖ := norm_sub_le _ _
        _ ≤ 81 / 16 * cJab L r₀ * cS * (Mj * gj * β1) + cr * Mj * gj * β1 := add_le_add hc2' hrN
        _ = (81 / 16 * cJab L r₀ * cS + cr) * Mj * gj * β1 := by ring
    · -- item (d)
      rw [hP, norm_one, mul_one]
      set β1 := ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ with hβ1
      set Mj := ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ with hMj
      set gj := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 with hgj
      set Z := (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z with hZd
      have hZ : Z ≠ 0 := lastOut_Z_ne (R.withMsq m) hρ0 hρ1 Nh _
      have hZn : 0 < ‖Z‖ := norm_pos_iff.2 hZ
      have hc := zCc_ge R hNh hm0 b μ₀ hK hmT hZ
      have hvB : vwB R m b μ₀ lam x = Mj * gj := rfl
      have hβx := hβ x hx h1 hj
      have hvA := hvwAeq x hx h1 hj
      have hβ10 : 0 ≤ β1 := norm_nonneg _
      have hVB0 : 0 ≤ Mj * gj := (hMb x hx h1 hj).le
      set cJ' := cJet L * (cRho L + 4 / r₀ ^ 2) with hcJ'd
      have hcJ'0 : 0 ≤ cJ' := by
        rw [hcJ'd]
        have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
        have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
        have hcS' : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
        have h1 : 0 ≤ cJet L := by
          unfold cJet; have := mul_nonneg hL2 (by linarith : (0 : ℝ) ≤ Q1 2); linarith
        have h2 : 0 ≤ cRho L := by
          unfold cRho
          have : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
          have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
          refine mul_nonneg hL2 ?_
          nlinarith
        exact mul_nonneg h1 (add_nonneg h2 (by positivity))
      set Λ := (L : ℝ) ^ (2 * N) with hΛd
      have hΛ : 0 < Λ := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
      have k1 : vwA R m b μ₀ x Nh * vwB R m b μ₀ lam x ≤
          2 * ((9 / 8) ^ 2 * R.ℓ ^ 2 / ‖Z‖) * (2 * β1) * (Mj * gj) := by
        rw [hvA, hvB]
        have := mul_le_mul hsc2 hβx (norm_nonneg _) (by positivity)
        have := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2)
        have := mul_le_mul_of_nonneg_right this hVB0
        nlinarith
      have hmAB' : 81 / 16 * cJ' * cS * R.ℓ ^ 2 ≤ 1 / (2 * m * Λ) := by
        rw [le_div_iff₀ (by positivity)]
        have e : 81 / 16 * cJ' * cS * R.ℓ ^ 2 * (2 * m * Λ) =
            2 * (81 / 16 * cJ' * cS * R.ℓ ^ 2) * m * Λ := by ring
        rw [e]; exact hmAB
      have hmid : 1 / (2 * m * Λ) / ‖Z‖ ≤ ‖zCc R Nh m b μ₀‖ := by
        refine le_trans (le_of_eq ?_) hc
        field_simp
        exact (div_self hZn.ne').symm
      calc ‖ε (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab‖
          ≤ cJ' * cS * (vwA R m b μ₀ x Nh * vwB R m b μ₀ lam x) := hε
        _ ≤ cJ' * cS * (2 * ((9 / 8) ^ 2 * R.ℓ ^ 2 / ‖Z‖) * (2 * β1) * (Mj * gj)) :=
            mul_le_mul_of_nonneg_left k1 (mul_nonneg hcJ'0 (by linarith))
        _ = (81 / 16 * cJ' * cS * R.ℓ ^ 2) / ‖Z‖ * (Mj * gj * β1) := by ring
        _ ≤ (1 / (2 * m * Λ)) / ‖Z‖ * (Mj * gj * β1) := by
            gcongr
        _ ≤ ‖zCc R Nh m b μ₀‖ * (Mj * gj * β1) := by gcongr
        _ = 1 * Mj * gj * (‖zCc R Nh m b μ₀‖ * β1) := by ring
  · -- the last-step defect
    obtain ⟨s', hs', hsc1, hsc2, hc2, hε, hLD⟩ := hxB x hx h1 hj
    have h0 := hvwA x hx h1 hj
    have hVB0 : 0 ≤ vwB R m b μ₀ lam x := (hMb x hx h1 hj).le
    have hcL : 0 ≤ cLab L * cS := by
      unfold cLab
      have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
      have : 0 ≤ (L : ℝ) ^ 2 * (2 * Q1 2 + 5 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) := by positivity
      exact mul_nonneg this (by linarith)
    refine hLD.trans ?_
    have hMj0 : 0 ≤ ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ := norm_nonneg _
    have k1 : vwA R m b μ₀ x Nh * vwB R m b μ₀ lam x ≤
        cu * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ * vwB R m b μ₀ lam x := by
      refine mul_le_mul_of_nonneg_right (h0.trans ?_) hVB0
      exact mul_le_of_le_one_right (mul_nonneg hcu hMj0) hg1
    calc cLab L * cS * (vwA R m b μ₀ x Nh * vwB R m b μ₀ lam x)
        ≤ cLab L * cS * (cu * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
          vwB R m b μ₀ lam x) := mul_le_mul_of_nonneg_left k1 hcL
      _ = cLab L * cS * cu * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 := by
          unfold vwB; ring

end Traj

end

end Spin2
