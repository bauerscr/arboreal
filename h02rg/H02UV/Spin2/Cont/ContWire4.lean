import Spin2.Cont.ContWire2

set_option autoImplicit false

/-!
# B3, T6 (a) wiring: the `a`-sector sizes of the restarted history in its own envelope

**`MasterCore.cw2_aSizes`**: for the data of `MasterCore.restartDT_lin` and `i ≤ N_h − m_r`,
with `M_a := 2s_{m_r+i}²M_i` (`M_i = M₀∏_{l<i}|1 − 𝔫F_{m_r+l}|`), the `a`-parts of the restarted
state `o = obsHistFrom R' P m_r o' (m_r+i) t` satisfy
`T(V(q)_a) ≤ M_a`, `T(𝒲(q)_a) ≤ (c_W(cǧ_{m_r+i}) + w/(s_{m_r}²M₀))M_a`,
`A^{(|𝓑(X)|−4)_+}T(K(X)_a) ≤ ((k + 120B(cε)w)/(s_{m_r}²M₀) + 8c_WB(cǧ_{m_r+i})²)M_a`
(the transients enter only through `w/(s²M₀)`, `k/(s²M₀)`, uniformly in `i`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L : ℕ} [NeZero L]

set_option maxHeartbeats 1000000 in
/-- **The `a`-sector sizes of the restarted history in its own envelope.** -/
theorem MasterCore.cw2_aSizes (D : MasterCore L) (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = D.ℓ) (hRA : R.A = D.A)
    (hRρ : R.ρ = D.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N)
    (b μ₀ : ℝ) (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (mr : ℕ) (o' : Obs2.ObsSt .two L N)
    (hmr0 : 0 < mr) (hmrN : mr ≤ Nh) (h0 : o'.IsObs) (hl0 : ObsLocInv P mr o')
    (hs0 : ObsSymInv mr o')
    (hf0 : ∀ b, Obs2.Loc2Form P.a (o'.V b : Obs.SA .two (Lam 2 L N)).a)
    (hp0 : ∀ b, (o'.V b : Obs.SA .two (Lam 2 L N)).a =
      Obs.LocObs.mass2 (o'.V b : Obs.SA .two (Lam 2 L N)).a • Obs.LocObs.pbp P.a)
    {M₀ k w : ℝ} (hM0 : 0 < M₀) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hb : ‖Obs2.betaTot2 (L := L) (N := N) mr
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr)‖ +
        Obs2.shareDev2 P.a mr
          (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr) ≤ M₀)
    (hW : WbHF (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr w)
    (hK : KbHF (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr k)
    (hg : D.rdtC * (D.cWo * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ mr).1) * 2) ≤ 1 / 1344)
    (hM : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + D.rdtΓ * w) ≤
      histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀) :
    ∀ i ≤ Nh - mr,
      (∀ q ∈ blockIdx (L := L) (N := N) (mr + i),
        Tj 2 (L : ℝ) (mr + i) (histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (((obsHistFrom (R.withMsq m) P mr o' (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V q : Obs.OE .two (Lam 2 L N)) : Obs.SA .two (Lam 2 L N)).a ≤ ENNReal.ofReal (2 * histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + i)‖) i)) ∧
      (∀ q ∈ blockIdx (L := L) (N := N) (mr + i),
        Tj 2 (L : ℝ) (mr + i) (histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (((obsHistFrom (R.withMsq m) P mr o' (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W q : Obs.OE .two (Lam 2 L N)) : Obs.SA .two (Lam 2 L N)).a ≤
          ENNReal.ofReal ((D.cWo * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (mr + i)).1) +
            w / (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀)) * (2 * histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + i)‖) i))) ∧
      (∀ X, IsConn (mr + i) X → ENNReal.ofReal ((R.withMsq m).A ^ (nb (mr + i) X - 2 ^ 2)) *
        Tj 2 (L : ℝ) (mr + i) (histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (((obsHistFrom (R.withMsq m) P mr o' (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X : Obs.OE .two (Lam 2 L N)) : Obs.SA .two (Lam 2 L N)).a ≤
          ENNReal.ofReal (((k + 120 * D.Bk * (D.c * D.ε) * w) /
              (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀) +
            8 * D.cWo * D.Bk * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (mr + i)).1) ^ 2) *
            (2 * histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + i)‖) i))) ∧
      0 < Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + i)‖) i := by
  intro i hi
  obtain ⟨⟨hA, hrat, henvp⟩, hW, hK⟩ := D.cw2_restartDT_lin N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD
    P V mr o' hmr0 hmrN h0 hl0 hs0 hf0 hp0 hM0 hk hw hb hW hK hg hM i hi
  set env := Obs2.rkEnv M₀ (fun i => ‖1 - Obs2.frakN2F P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) mr (mr + i)‖) i with henvd
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id D.hC2
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = D.ρ from hRρ]; exact hρpos.le
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = D.ρ from hRρ]; exact hρ8'
  have hs : 0 < histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) := histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (mr + i)
  have hs0' : 0 < histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) := histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) mr
  have henv : 0 ≤ env := mul_nonneg hM0.le (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hX : 0 < histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀ := by positivity
  have hMa : 0 ≤ 2 * histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * env := by positivity
  -- transient ratio
  have htr : ∀ x : ℝ, 0 ≤ x → ∀ q : ℝ, 0 ≤ q → q * (7 / 5) ≤ 1 →
      q ^ i * x ≤ x / (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀) * (2 * histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * env) := by
    intro x hx q hq hq1
    rw [div_mul_eq_mul_div, le_div_iff₀ hX]
    have h1 : (q * (7 / 5)) ^ i ≤ 1 := pow_le_one₀ (by positivity) hq1
    have h2 : q ^ i * (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀) ≤ q ^ i * ((7 / 5) ^ i * (histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * env)) :=
      mul_le_mul_of_nonneg_left hrat (by positivity)
    have hse : 0 ≤ histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * env := by positivity
    have h3 : q ^ i * ((7 / 5) ^ i * (histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * env)) ≤ 2 * histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * env := by
      have e : q ^ i * ((7 / 5) ^ i * (histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * env)) = (q * (7 / 5)) ^ i * (histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * env) := by
        rw [mul_pow]; ring
      rw [e]
      have := mul_le_mul_of_nonneg_right h1 hse
      linarith
    have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hx
    calc q ^ i * x * (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀) = x * (q ^ i * (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * M₀)) := by ring
      _ ≤ x * (2 * histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * env) := h4
  have hcW : 0 ≤ D.cWo := le_trans zero_le_one D.consts_nonneg.2.2.2.2.2.1
  have hBk : 0 ≤ D.Bk := D.consts_nonneg.2.2.2.2.2.2.1
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun X hX' => ?_, henvp⟩
  · rw [obsHistF2_pure (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) hf0 hp0 (mr + i) (by omega) q]
    refine (Tj_smul_pbp_le (mr + i) hs _ _).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : ‖Obs.LocObs.mass2 (((obsHistFrom (R.withMsq m) P mr o' (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V q : Obs.OE .two (Lam 2 L N)) : Obs.SA .two (Lam 2 L N)).a‖ ≤
        Obs2.shA2 (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (mr + i) := by
      rw [← histVF2_a (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (mr + i) q]
      exact Finset.single_le_sum (f := fun c => ‖Obs.LocObs.mass2
        (histVF2 (R.withMsq m) P mr o' (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (mr + i) c : Obs.SA .two (Lam 2 L N)).a‖)
        (fun _ _ => norm_nonneg _) hq
    have := mul_le_mul_of_nonneg_right (h1.trans hA) (sq_nonneg (histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    nlinarith
  · have h := hW q hq
    rw [Obs2.oTo_wA] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have := htr w hw (1 / 6) (by norm_num) (by norm_num)
    rw [add_mul]
    linarith
  · have h := hK X hX'
    rw [Obs2.oTo_wA] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hk' : 0 ≤ k + 120 * D.Bk * (D.c * D.ε) * w := by
      have : 0 ≤ D.c * D.ε := by
        obtain ⟨H, -, -⟩ := D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
        have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.C₂x = D.c := by
          rw [D.hc]; exact cR_congr (show R.ℓ = D.ℓ from hRℓ) _ _ _
        have hc2 : 2 ≤ D.c := hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
        have hε0 : 0 ≤ D.ε := by have := H.hε; linarith
        positivity
      positivity
    have := htr _ hk' (8 / 15) (by norm_num) (by norm_num)
    have h15 : 15 * D.cWo * D.Bk * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (mr + i)).1) ^ 2 * (histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * env) ≤ 8 * D.cWo * D.Bk * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (mr + i)).1) ^ 2 * (2 * histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * env) := by
      have : 0 ≤ D.cWo * D.Bk * (D.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (mr + i)).1) ^ 2 * (histS (R.withMsq m) (mr + i) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * env) := by positivity
      nlinarith
    rw [add_mul]
    linarith

end

end Spin2
