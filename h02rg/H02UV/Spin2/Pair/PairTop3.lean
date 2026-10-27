import Spin2.Pair.PairTop2

/-!
# Top coalescence: the bound `|E| ≤ K‖M_{N_h}‖²ǧ_{N_h}` from the seed sizes at `N - 1`

Pair observable at `x` with `j_x ≥ N_h + 1`, the reduced state `oTop … dxTop` at `N_h + 1`, `h = 0`
(`r = 0`), `M = ‖M_{N_h}‖`, `g = ǧ_{N_h}`. Weights `M_a ≤ 2s_{N_h}²|β_{a,N_h}|`, `M_a, M_b ≤ c_uMg`.

* **`zero_top_pure`** (pure): with `P₀ = 1`, `r' = 0`: `‖(x_{ab} - c·y_{ab})/s‖ ≤
  (4e₂ + 4e₁)Mg‖(x_a - c·y_a)/s‖` (`zero_rel_pureW`, `zm_red_elim`, `zm_rel_boundW`).
* **`pairTop_E_le`** (one trajectory, one `x`): from the seed size
  `A^{(|𝓑(X)|-4)_+}‖K'_{N_h+1}(X)‖_{wM(M_a,M_b)} ≤ c_K`, the one-point items of the last step at `x`
  (`P₀ = 1`, `‖c2F_a - β_{N-1}‖ ≤ ½|β_{N-1}|`, `‖εF_a‖ ≤ K_A|β_{N-1}|/|Z_N|`), `‖γ_{a,N}‖ ≤ K₄M`,
  `Case2TopStep`, the last-step smallness and the mass windows:
  `b⟨ψ̄_0ψ_x⟩ = γ_{0,N-1}γ_{x,N-1} - E`, `‖E‖ ≤ (c_{Lab}c_Sc_u² + 4(c_u + e₁)K₄)M²g`,
  `c_S = 8c_K + 1`, `e₁ = (81/16)c_{Jab}c_Sc_u`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L N : ℕ} [NeZero L]

/-- **The reduced zero mode at `P₀ = 1`, `r' = 0`** (pure). -/
theorem zero_top_pure {ya yab xa xab β cc s : ℂ} {e1 e2 M g : ℝ} (hβ : β ≠ 0)
    (hM : 0 ≤ M) (hg : 0 ≤ g) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (h1 : ‖ya - β‖ ≤ 1 / 2 * ‖β‖) (h2 : ‖yab‖ ≤ e1 * M * g * ‖β‖)
    (h3 : ‖xab‖ ≤ e2 * M * g * (‖cc‖ * ‖β‖)) (h4 : ‖xa‖ ≤ 1 / 4 * (‖cc‖ * ‖β‖)) :
    ‖(xab - cc * yab) / s‖ ≤ (4 * e2 + 4 * e1) * M * g * ‖(xa - cc * ya) / s‖ := by
  obtain ⟨ρ, hρ, hρn, hx⟩ := zero_rel_pureW (P0 := 1) (r := 0) (cr := 0) hβ one_ne_zero hM hg
    le_rfl he1 he2 (by simpa using h1) (by simpa using h2) (by simp)
    (by simpa using h3) (by simpa using h4)
  rw [PtCorr2.zm_red_elim hρ]
  have hK : ‖xab - ρ * xa‖ ≤ (4 * e2 + 2 * (0 + e1)) * M * g * ‖xa - cc * ya‖ := hx
  have := zm_rel_boundW (s := s) hK hρn
  refine this.trans (le_of_eq ?_)
  ring

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

set_option maxHeartbeats 8000000 in
/-- **The pair part for `j_x ≥ N_h + 1`** (one trajectory, one `x`, `h = 0`). -/
theorem pairTop_E_le {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Cf cW cK0 r₀ : ℝ} (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hb : 0 < b) (hh0 : b = μ₀ + m)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) (hLp : pauliL0 2 ≤ L)
    (hL8 : 2 ^ (2 + 3) + 8 * 2 < L) (hA2 : 2 ≤ R.A)
    (hmN : |(R.withMsq m).msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1)
    (hG : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (R.A / 2) r₀)
    (hcW : 0 ≤ cW) (hcK0 : 0 ≤ cK0) (hCf : 0 ≤ Cf)
    (hg0 : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1)
    (hs1 : 2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ R.ρ)
    (hs2 : 8 * cM * R.ℓ ^ 2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 / 2)
    (hs3 : cRho L * (cTauL R.ℓ Cf cW cK0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1)
    (hs4 : 4 * (cTauL R.ℓ Cf cW cK0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ r₀ ^ 2)
    (hs5 : cTauL R.ℓ Cf cW cK0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ r₀)
    (lam : ℕ → ℂ) (x : Lam 2 L N) (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    {Ma Mb cK cu K4 KA : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) (hcK : 0 ≤ cK) (hcu : 0 ≤ cu)
    (hKo : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Obs2.oTo (wM Ma Mb) (Nh + 1)
        (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((oTop R Nh m b μ₀ (dxTop Nh) x).K X) ≤ ENNReal.ofReal cK)
    (hMa2 : Ma ≤ 2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
      ‖hBeta R m b μ₀ x Nh‖)
    (hMaM : Ma ≤ cu * ‖Mmag R m b μ₀ lam Nh‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hMbM : Mb ≤ cu * ‖Mmag R m b μ₀ lam Nh‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (htop : Case2TopStep R (ptsX x) (zV b) Nh m b μ₀)
    (hβ0 : hBeta R m b μ₀ x Nh ≠ 0)
    (hone1 : ‖Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a -
        Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ ≤
      1 / 2 * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖)
    (hone2 : ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      KA * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ /
        ‖(lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖)
    (hgam : ‖gamNa R Nh m b μ₀ x‖ ≤ K4 * ‖Mmag R m b μ₀ lam Nh‖)
    (hCN : lC R Nh m b μ₀ x x = lC R Nh m b μ₀ 0 0)
    {Kt : ℝ}
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2) (hmA : 8 * KA * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (8 * cK + 1) *
      R.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) :
    ∃ E : ℂ, (b : ℂ) * PtCorr2.avg0 L N m b μ₀ (psibar 0 * psi x) =
        uA R m b μ₀ x (Nh + 1) * uB R m b μ₀ x (Nh + 1) - E ∧
      ‖E‖ ≤ (cLab L * (8 * cK + 1) * cu ^ 2 +
          4 * (cu + 81 / 16 * cJab L r₀ * (8 * cK + 1) * cu) * K4) *
        ‖Mmag R m b μ₀ lam Nh‖ ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by
  have hρ0 : 0 ≤ (R.withMsq m).ρ := hVL.2.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set oT := oTop R Nh m b μ₀ (dxTop Nh) with hoT
  set Mn := ‖Mmag R m b μ₀ lam Nh‖ with hMn
  set g := (t Nh).1 with hgd
  have hMn0 : 0 ≤ Mn := norm_nonneg _
  -- the exact split
  obtain ⟨p, r, hp0, hpr, -, hr, hX0, hΩ0, hΩΩ, hX'0, hnA, hP⟩ :=
    pairTop_E R hNh m hρ1 hspl hm0 hm hV hVL hL8 hb (le_of_eq hh0) (dxTop Nh) x
      (dCov_dxTop Nh x) hj
  have hr0 : (r : ℂ) = 0 := by
    rw [← hr, PtCorr2.onept_avg0_h0 hb hm0 hh0, mul_one_div_cancel
      (Complex.ofReal_ne_zero.2 hb.ne'), sub_self]
  have hr0' : r = 0 := by exact_mod_cast hr0
  have hp : (p : ℂ) = 0 := by
    have : p = 0 := le_antisymm (hr0' ▸ hpr) hp0
    rw [this, Complex.ofReal_zero]
  rw [hr0, hp] at hP
  rw [hr0, zero_sub] at hnA
  refine ⟨PtCorr2.nAB (zCstR R Nh m b μ₀ oT x) + PtCorr2.nAB (zZmR R Nh m b μ₀ oT x), ?_, ?_⟩
  · rw [hP]; ring
  -- the reduced constants
  have hF : PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oT x)
      (Nh + 1) t = oT x := PtCorr2.obsHistFrom_le (oT x) t hj
  have habT : PtCorr2.ObsAbInv (Nh + 1) (oT x) :=
    PtCorr2.obsAbInv_redTop (R.withMsq m) (ptsX x) _ _ Nh t
  have hlocT : PtCorr2.ObsLocInv (ptsX x) (Nh + 1) (oT x) :=
    PtCorr2.obsLocInv_redTop (R.withMsq m) (ptsX x) hV hVL hVN _
      (PtCorr2.obsLocInv_init .two (zV b) (ptsX x)) t _
  obtain ⟨-, hXd⟩ := nAB_zCstR_top R Nh m b μ₀ oT x hj habT rfl hX'0 hCN
  -- the last step
  obtain ⟨s', hs', hsc1, hsc2, hc2, hε, hLD⟩ := pairLastAB_xT R hNh hV hVL hVN hLp hL8 hA2 hmN hG
    hr₀ hr₀1 hJ hcW hcK0 hCf hg0 hg1 hs1 hs2 hs3 hs4 hs5 oT x
    (PtCorr2.redTop_isObs (R.withMsq m) (ptsX x) _ _ Nh t) (by rw [hF]; exact hlocT)
    (by rw [hF]; exact habT) hMa hMb le_rfl le_rfl hcK
    (fun b' _ => by rw [hF]; show Obs2.oTo _ _ _ (0 : Obs.OE .two (Lam 2 L N)) ≤ _
                    rw [Obs2.oTo_zero']; exact zero_le)
    (fun b' _ => by rw [hF]; show Obs2.oTo _ _ _ (0 : Obs.OE .two (Lam 2 L N)) ≤ _
                    rw [Obs2.oTo_zero']; exact zero_le)
    (fun X hX => by rw [hF]; exact hKo X hX)
  simp only [zero_add] at hc2 hε hLD
  set cS := 8 * cK + 1 with hcSd
  have hcS : 1 ≤ cS := by rw [hcSd]; linarith
  -- the coupling `β_{a,N-1}`
  set β1 := ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ with hβ1d
  have hβx : ‖hBeta R m b μ₀ x Nh‖ ≤ 2 * β1 := by
    set P := ptsX (L := L) (N := N) x
    have hflow := bt2_flow R P (zV b) (Nh := Nh + 1) (by omega) m b μ₀ (k := Nh) (by omega)
    have hBB : ‖bt2 R P (zV b) m b μ₀ Nh‖ ≤ 2 * ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ := by
      rw [hflow]; exact beta_step_ge htop.1 htop.2
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
    rw [hβ1d, hβeq]; exact hBB
  have hβ10 : 0 < β1 := by
    have := norm_pos_iff.2 hβ0
    linarith
  have hβ1ne : Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) ≠ 0 := norm_pos_iff.1 hβ10
  -- the constants
  have hcJ0 : 0 ≤ cJab L r₀ := by
    unfold cJab
    have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
    have hcS' : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
    have h1 : 0 ≤ cJet L := by
      unfold cJet; have := mul_nonneg hL2 (by linarith : (0 : ℝ) ≤ Q1 2); linarith
    have h2 : 0 ≤ cRho L := by
      unfold cRho
      have h4 : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
      have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
      refine mul_nonneg hL2 ?_
      linarith only [h4, h3, hcS', hQ1]
    have := mul_nonneg h1 (add_nonneg h2 (by positivity : (0 : ℝ) ≤ 4 / r₀ ^ 2))
    positivity
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
      have h4 : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
      have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
      refine mul_nonneg hL2 ?_
      linarith only [h4, h3, hcS', hQ1]
    exact mul_nonneg h1 (add_nonneg h2 (by positivity))
  have hcL : 0 ≤ cLab L := by
    unfold cLab
    have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
    positivity
  have hMg : 0 ≤ cu * Mn * g := mul_nonneg (mul_nonneg hcu hMn0) hg0.le
  set e1 := 81 / 16 * cJab L r₀ * cS * cu with he1d
  have he1 : 0 ≤ e1 := by rw [he1d]; positivity
  -- item (c): `|c2F'_{ab}| ≤ e₁Mg|β|`
  have hs'2 : 0 < s' ^ 2 := by positivity
  have hc2' : ‖Suscept.c2 (zFinR R Nh m b μ₀ oT x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
      e1 * Mn * g * β1 := by
    have k1 : Ma * Mb ≤ (81 / 16 * β1) * s' ^ 2 * (cu * Mn * g) := by
      have hMa' : Ma ≤ 2 * ((9 / 8) ^ 2 * s' ^ 2) * (2 * β1) := by
        refine hMa2.trans ?_
        have := mul_le_mul hsc1 hβx (norm_nonneg _) (by positivity)
        nlinarith
      have := mul_le_mul hMa' hMbM hMb.le (by positivity)
      calc Ma * Mb ≤ 2 * ((9 / 8) ^ 2 * s' ^ 2) * (2 * β1) * (cu * Mn * g) := this
        _ = (81 / 16 * β1) * s' ^ 2 * (cu * Mn * g) := by ring
    have k2 : s' ^ 2 * ‖Suscept.c2 (zFinR R Nh m b μ₀ oT x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
        s' ^ 2 * (e1 * Mn * g * β1) := by
      refine hc2.trans ?_
      have := mul_le_mul_of_nonneg_left k1 (mul_nonneg hcJ0 (by linarith : (0 : ℝ) ≤ cS))
      calc cJab L r₀ * cS * (Ma * Mb) ≤
            cJab L r₀ * cS * ((81 / 16 * β1) * s' ^ 2 * (cu * Mn * g)) := this
        _ = s' ^ 2 * (e1 * Mn * g * β1) := by rw [he1d]; ring
    exact le_of_mul_le_mul_left k2 hs'2
  -- item (d): `|εF'_{ab}| ≤ c_uMg|c||β|`
  set Z := (lastOut (R.withMsq m) Nh t).Z with hZd
  have hZ : Z ≠ 0 := lastOut_Z_ne (R.withMsq m) hρ0 hρ1 Nh _
  have hZn : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  have hc := zCc_ge R hNh hm0 b μ₀ hK hmT hZ
  set Λ := (L : ℝ) ^ (2 * N) with hΛd
  have hΛ : 0 < Λ := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hmid : 1 / (2 * m * Λ) / ‖Z‖ ≤ ‖zCc R Nh m b μ₀‖ := by
    refine le_trans (le_of_eq ?_) hc
    field_simp
    exact (div_self hZn.ne').symm
  have hε' : ‖ε (zFinR R Nh m b μ₀ oT x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
      cu * Mn * g * (‖zCc R Nh m b μ₀‖ * β1) := by
    have k1 : Ma * Mb ≤ 2 * ((9 / 8) ^ 2 * R.ℓ ^ 2 / ‖Z‖) * (2 * β1) * (cu * Mn * g) := by
      have hMa' : Ma ≤ 2 * ((9 / 8) ^ 2 * R.ℓ ^ 2 / ‖Z‖) * (2 * β1) := by
        refine hMa2.trans ?_
        have := mul_le_mul hsc2 hβx (norm_nonneg _) (by positivity)
        nlinarith
      exact mul_le_mul hMa' hMbM hMb.le (by positivity)
    have hmAB' : 81 / 16 * cJ' * cS * R.ℓ ^ 2 ≤ 1 / (2 * m * Λ) := by
      rw [le_div_iff₀ (by positivity)]
      have e : 81 / 16 * cJ' * cS * R.ℓ ^ 2 * (2 * m * Λ) =
          2 * (81 / 16 * cJ' * cS * R.ℓ ^ 2) * m * Λ := by ring
      rw [e]; exact hmAB
    calc ‖ε (zFinR R Nh m b μ₀ oT x : Obs.SA .two (Lam 2 L N)).ab‖
        ≤ cJ' * cS * (Ma * Mb) := hε
      _ ≤ cJ' * cS * (2 * ((9 / 8) ^ 2 * R.ℓ ^ 2 / ‖Z‖) * (2 * β1) * (cu * Mn * g)) :=
          mul_le_mul_of_nonneg_left k1 (mul_nonneg hcJ'0 (by linarith))
      _ = (81 / 16 * cJ' * cS * R.ℓ ^ 2) / ‖Z‖ * (cu * Mn * g * β1) := by ring
      _ ≤ (1 / (2 * m * Λ)) / ‖Z‖ * (cu * Mn * g * β1) := by gcongr
      _ ≤ ‖zCc R Nh m b μ₀‖ * (cu * Mn * g * β1) := by gcongr
      _ = cu * Mn * g * (‖zCc R Nh m b μ₀‖ * β1) := by ring
  -- item (e): `|εF_a| ≤ ¼|c||β|`
  have he' : ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      1 / 4 * (‖zCc R Nh m b μ₀‖ * β1) := by
    have hKA : KA * (β1 / ‖Z‖) ≤ 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * β1 := by
      have hKA0 : KA ≤ 1 / (8 * m * Λ) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have hq : 0 ≤ β1 / ‖Z‖ := div_nonneg hβ10.le hZn.le
      have e : 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * β1 = 1 / (8 * m * Λ) * (β1 / ‖Z‖) := by
        field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hKA0 hq
    have hc' : 1 / (2 * m * ‖Z‖ * Λ) ≤ ‖zCc R Nh m b μ₀‖ := by
      refine le_trans (le_of_eq ?_) hmid
      field_simp
    calc ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤ KA * β1 / ‖Z‖ := hone2
      _ = KA * (β1 / ‖Z‖) := by ring
      _ ≤ 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * β1 := hKA
      _ ≤ 1 / 4 * ‖zCc R Nh m b μ₀‖ * β1 := by gcongr
      _ = 1 / 4 * (‖zCc R Nh m b μ₀‖ * β1) := by ring
  -- the reduced zero mode
  set F := zFin R Nh m b μ₀ x with hFd
  set F' := zFinR R Nh m b μ₀ oT x with hF'd
  set cc := zCc R Nh m b μ₀ with hccd
  obtain ⟨s1, s2, -, -⟩ := PtCorr2.sX_omegaCO_cstC cc F
  obtain ⟨-, -, -, s4'⟩ := PtCorr2.sX_omegaCO_cstC cc F'
  have hΩd : zZm R Nh m b μ₀ x = PtCorr2.omegaCO (PtCorr2.cstC (Lam 2 L N) cc) F := rfl
  have hΩd' : zZmR R Nh m b μ₀ oT x = PtCorr2.omegaCO (PtCorr2.cstC (Lam 2 L N) cc) F' := rfl
  have hnAΩ : PtCorr2.nA (zZm R Nh m b μ₀ x) =
      (ε (F : Obs.SA .two (Lam 2 L N)).a - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).a) /
      (ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e) := by
    unfold PtCorr2.nA; rw [hΩd, s1, s2]
  have hnABΩ : PtCorr2.nAB (zZmR R Nh m b μ₀ oT x) =
      (ε (F' : Obs.SA .two (Lam 2 L N)).ab - cc * Suscept.c2 (F' : Obs.SA .two (Lam 2 L N)).ab) /
      (ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e) := by
    unfold PtCorr2.nAB
    rw [hΩΩ, hΩd, s1, hΩd', s4']
  have hZm := zero_top_pure (s := ε (F : Obs.SA .two (Lam 2 L N)).e -
      cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e) hβ1ne hMn0 hg0.le he1 hcu
    hone1 hc2' hε' he'
  rw [← hnABΩ, ← hnAΩ, hnA, norm_neg] at hZm
  -- assembly
  have hD1 : ‖PtCorr2.nAB (zCstR R Nh m b μ₀ oT x)‖ ≤ cLab L * cS * cu ^ 2 * Mn ^ 2 * g := by
    rw [hXd]
    refine hLD.trans ?_
    have hMaM' : Ma * Mb ≤ (cu * Mn * g) * (cu * Mn * g) :=
      mul_le_mul hMaM hMbM hMb.le hMg
    have hg2 : (cu * Mn * g) * (cu * Mn * g) ≤ cu ^ 2 * Mn ^ 2 * g := by
      have : g * g ≤ g := mul_le_of_le_one_left hg0.le hg1
      have h0 : 0 ≤ cu ^ 2 * Mn ^ 2 := by positivity
      have e : (cu * Mn * g) * (cu * Mn * g) = cu ^ 2 * Mn ^ 2 * (g * g) := by ring
      rw [e]; exact mul_le_mul_of_nonneg_left this h0
    have := mul_le_mul_of_nonneg_left (hMaM'.trans hg2) (mul_nonneg hcL (by linarith : (0:ℝ) ≤ cS))
    calc cLab L * cS * (Ma * Mb) ≤ cLab L * cS * (cu ^ 2 * Mn ^ 2 * g) := this
      _ = cLab L * cS * cu ^ 2 * Mn ^ 2 * g := by ring
  have hD2 : ‖PtCorr2.nAB (zZmR R Nh m b μ₀ oT x)‖ ≤ 4 * (cu + e1) * K4 * Mn ^ 2 * g := by
    refine hZm.trans ?_
    have h0 : 0 ≤ (4 * cu + 4 * e1) * Mn * g := by positivity
    have := mul_le_mul_of_nonneg_left hgam h0
    calc (4 * cu + 4 * e1) * Mn * g * ‖gamNa R Nh m b μ₀ x‖ ≤
          (4 * cu + 4 * e1) * Mn * g * (K4 * Mn) := this
      _ = 4 * (cu + e1) * K4 * Mn ^ 2 * g := by ring
  calc ‖PtCorr2.nAB (zCstR R Nh m b μ₀ oT x) + PtCorr2.nAB (zZmR R Nh m b μ₀ oT x)‖
      ≤ ‖PtCorr2.nAB (zCstR R Nh m b μ₀ oT x)‖ + ‖PtCorr2.nAB (zZmR R Nh m b μ₀ oT x)‖ :=
        norm_add_le _ _
    _ ≤ cLab L * cS * cu ^ 2 * Mn ^ 2 * g + 4 * (cu + e1) * K4 * Mn ^ 2 * g := add_le_add hD1 hD2
    _ = (cLab L * cS * cu ^ 2 + 4 * (cu + e1) * K4) * Mn ^ 2 * g := by ring

end Traj

end

end Spin2
