import Spin2.Gam.LastOneRem
import PtCorr2.Last.LastObsK6

/-!
# PR6, item (b): the activity of the observable last step — `LastKRem` from block sizes

Pair observable at `x`, last step `j = N_h + 1` (`C = C_N`, inputs `V, 𝒲, K` of scale `N - 1`).
The activity `K_N(Λ) = Knext2O(Λ)` of the map with localisation has no norm bound (the lifted
coordinates of `Loc_{Λ,B}` wrap around the torus), but its `σ_a` jets are those of `F_N` minus
`∑_Bm₂V_N(B)_a` (`PtCorr2.finO_last_TI`), and `F_N = e^{u(Λ)}e^{-u'(Λ)}(∏_BG'(B) + K'(Λ))` with the
reference map without localisation (`PtCorr2.finG_eq`); `PtCorr2.LastJetBd` bounds these jets
by the input sizes (`PtCorr2.finG_jets_le`).

* Named input **`LastL1 c_A`** (open: the `ℓ¹` size of the shares at `N_h + 1`, i.e. the phase
  alignment at the step `N_h`): `∑_B|m₂V_{N_h+1}(B)_a| ≤ c_A|β_{N_h+1}|`.
* `KbHc` at `N_h + 1` relative to `ǧ_{N_h}s_{N_h}²|β_{N_h}|` (the `K^{obs}` analogue of
  `LastObsConclW`).
* **`lastKRem_x`**, **`lastKRem_of`**: from `LastJetBd L (A/2) r₀`, `GlueOut`, the block bounds of
  `𝒲^{obs}_{N_h+1}`, `K^{obs}_{N_h+1}`, `LastL1 c_A`, `Case2TopStep` and the smallness of
  `ǧ_{N_h}`: `LastKRem K_A` with `K_A = c_J(c_ρ + 4/r₀²)c_τ(9/8)c_A(1 + ℓ²)`,
  `c_τ = (4c_Mℓ² + 8ℓ⁴)C_f + 10C_f + (9/4)c_W + 18c_K + 1`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **Named input (open): the `ℓ¹` size of the shares at `N_h + 1`.** -/
def LastL1 (Nh : ℕ) (m b μ₀ cA : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    Obs2.shA2 (Obs2.histVO2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (Nh + 1) ≤
      cA * ‖bt2 R (ptsX x) (zV b) m b μ₀ (Nh + 1)‖

/-- The size constant `c_τ` of the inputs of the last step. -/
def cTauL (ℓ Cf cW cK : ℝ) : ℝ :=
  (4 * cM * ℓ ^ 2 + 8 * ℓ ^ 4) * Cf + 10 * Cf + 9 / 4 * cW + 18 * cK + 1

/-- The constant `K_A` of `LastKRem`. -/
def cKAL (L : ℕ) (ℓ r₀ Cf cW cK cA : ℝ) : ℝ :=
  cJet L * (cRho L + 4 / r₀ ^ 2) * cTauL ℓ Cf cW cK * (9 / 8) * cA * (1 + ℓ ^ 2)

theorem le_of_forall_add_mul {X B C : ℝ} (hC : 0 ≤ C) (h : ∀ η : ℝ, 0 < η → X ≤ B + C * η) :
    X ≤ B := by
  by_contra hXB
  rw [not_le] at hXB
  have hη : 0 < (X - B) / (2 * (C + 1)) := div_pos (by linarith) (by linarith)
  have h1 := h _ hη
  have h2 : C * ((X - B) / (2 * (C + 1))) < X - B := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

theorem kA_arith_c2 {X s s' A1 β1 c τ cτ gg cA ℓ : ℝ} (hc : 0 ≤ c) (hτ : τ = cτ * gg)
    (hcτ : 0 ≤ cτ) (hgg : 0 ≤ gg) (hs' : 0 < s') (hss : s ^ 2 ≤ 9 / 8 * s' ^ 2)
    (hA : A1 ≤ cA * β1) (hX : ∀ η : ℝ, 0 < η → s' ^ 2 * X ≤ c * τ * (s ^ 2 * (A1 + η)))
    (hA0 : 0 ≤ A1) (hcAβ : 0 ≤ cA * β1) :
    X ≤ c * cτ * (9 / 8) * cA * (1 + ℓ ^ 2) * gg * β1 := by
  have hs2 : 0 < s' ^ 2 := by positivity
  have key : ∀ η : ℝ, 0 < η → X ≤ c * cτ * (9 / 8) * cA * gg * β1 + (c * cτ * (9 / 8) * gg) * η := by
    intro η hη
    have h1 := hX η hη
    have h2 : c * τ * (s ^ 2 * (A1 + η)) ≤ c * τ * (9 / 8 * s' ^ 2 * (cA * β1 + η)) := by
      have hτ0 : 0 ≤ c * τ := by rw [hτ]; positivity
      refine mul_le_mul_of_nonneg_left (mul_le_mul hss (by linarith) (by linarith) (by positivity)) hτ0
    have h3 : s' ^ 2 * X ≤ s' ^ 2 * (c * τ * (9 / 8) * (cA * β1 + η)) := by
      have := h1.trans h2; nlinarith
    have h4 := le_of_mul_le_mul_left h3 hs2
    rw [hτ] at h4; nlinarith
  have h := le_of_forall_add_mul (by positivity) key
  have hℓ : c * cτ * (9 / 8) * cA * gg * β1 ≤ c * cτ * (9 / 8) * cA * (1 + ℓ ^ 2) * gg * β1 := by
    have h0 : 0 ≤ c * cτ * (9 / 8) * gg * (cA * β1) := by positivity
    nlinarith [sq_nonneg ℓ]
  linarith

theorem kA_arith_eps {X s A1 β1 c τ cτ gg cA ℓ Zn : ℝ} (hc : 0 ≤ c) (hτ : τ = cτ * gg)
    (hcτ : 0 ≤ cτ) (hgg : 0 ≤ gg) (hgg1 : gg ≤ 1) (hZn : 0 < Zn)
    (hsZ : s ^ 2 ≤ 9 / 8 * ℓ ^ 2 / Zn)
    (hA : A1 ≤ cA * β1) (hX : ∀ η : ℝ, 0 < η → X ≤ c * τ * (s ^ 2 * (A1 + η)))
    (hA0 : 0 ≤ A1) (hcAβ : 0 ≤ cA * β1) :
    X ≤ c * cτ * (9 / 8) * cA * (1 + ℓ ^ 2) * β1 / Zn := by
  have key : ∀ η : ℝ, 0 < η →
      X ≤ c * cτ * (9 / 8) * cA * (1 + ℓ ^ 2) * β1 / Zn + (c * cτ * (9 / 8) * (1 + ℓ ^ 2) / Zn) * η := by
    intro η hη
    have h1 := hX η hη
    have hτ0 : 0 ≤ c * τ := by rw [hτ]; positivity
    have h2 : c * τ * (s ^ 2 * (A1 + η)) ≤ c * τ * (9 / 8 * ℓ ^ 2 / Zn * (cA * β1 + η)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hsZ (by linarith) (by linarith) (by positivity)) hτ0
    have h3 : c * τ * (9 / 8 * ℓ ^ 2 / Zn * (cA * β1 + η)) ≤
        c * cτ * (9 / 8) * (1 + ℓ ^ 2) / Zn * (cA * β1 + η) := by
      rw [hτ]
      have hq : 0 ≤ (cA * β1 + η) / Zn := by positivity
      have e1 : c * (cτ * gg) * (9 / 8 * ℓ ^ 2 / Zn * (cA * β1 + η)) =
          c * cτ * (9 / 8) * (gg * ℓ ^ 2) * ((cA * β1 + η) / Zn) := by ring
      have e2 : c * cτ * (9 / 8) * (1 + ℓ ^ 2) / Zn * (cA * β1 + η) =
          c * cτ * (9 / 8) * (1 + ℓ ^ 2) * ((cA * β1 + η) / Zn) := by ring
      rw [e1, e2]
      have : gg * ℓ ^ 2 ≤ 1 + ℓ ^ 2 := by nlinarith [sq_nonneg ℓ]
      have h0 : 0 ≤ c * cτ * (9 / 8) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h0) hq
    have e : c * cτ * (9 / 8) * (1 + ℓ ^ 2) / Zn * (cA * β1 + η) =
        c * cτ * (9 / 8) * cA * (1 + ℓ ^ 2) * β1 / Zn + (c * cτ * (9 / 8) * (1 + ℓ ^ 2) / Zn) * η := by
      ring
    linarith
  exact le_of_forall_add_mul (by positivity) key

set_option maxHeartbeats 8000000 in
/-- **The `σ_a` jets of the activity of the observable last step along one trajectory.** -/
theorem lastKRem_x {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Cf cW cK cA r₀ : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) (hLp : pauliL0 2 ≤ L)
    (hL8 : 2 ^ (2 + 3) + 8 * 2 < L)
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
    (x : Lam 2 L N) (hx1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hW : WbHc (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)
      (cW * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
        histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖))
    (hK : KbHc (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)
      (cK * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
        histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖))
    (htop : Case2TopStep R (ptsX x) (zV b) Nh m b μ₀)
    (hl1 : Obs2.shA2 (Obs2.histVO2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (Nh + 1) ≤
      cA * ‖bt2 R (ptsX x) (zV b) m b μ₀ (Nh + 1)‖) :
    ‖Suscept.c2 (zKN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
        cKAL L R.ℓ r₀ Cf cW cK cA * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
          ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ ∧
    ‖ε (zKN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      cKAL L R.ℓ r₀ Cf cW cK cA * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ /
        ‖(lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hA : 0 < R.A := Fact.out
  set R' := R.withMsq m with hR'
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set P := ptsX (L := L) (N := N) x with hPd
  set o₀ := Obs2.obsInit .two (zV b) P with ho₀
  set o := Obs2.obsHist R' P o₀ (Nh + 1) t with hod
  set st := (histOut R' Nh t).st with hst
  set gg := (t Nh).1 with hgg
  have ho : o.IsObs := Obs2.obsHist_isObs R' P o₀ (Obs2.obsInit_isObs .two (zV b) P) (Nh + 1) t
  have hρ0 : 0 ≤ R'.ρ := hVL.2.2.2.2.1
  have hρ8 : R'.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have H : RawInv R' (Nh + 1) st := rawInv_histU R' hV hVL t (Nh + 1) le_rfl
  obtain ⟨hC0, hCt, hCs, hCsym⟩ := LastN.covN hVN H
  have hjN : Nh + 1 < N := by omega
  have hD : (histOut R' Nh t).D ∈ BSub (L := L) (N := N) (Nh + 1) :=
    (RawInv.stepL hVL (rawInv_hist R' hρ0 Nh hV t) (t Nh).1 (t Nh).2.1 (rawD_mem R' _ _)
      (rawK_mem R' _ _)).2.1
  have hKm : (histOut R' Nh t).K ∈ ASub (L := L) (N := N) (Nh + 1) :=
    (RawInv.stepL hVL (rawInv_hist R' hρ0 Nh hV t) (t Nh).1 (t Nh).2.1 (rawD_mem R' _ _)
      (rawK_mem R' _ _)).2.2
  obtain ⟨⟨hz, hy, hnu, hgn, hgre, hWl, hDd, hKk⟩, -⟩ := hG
  have hg0' : 0 ≤ gg := hg0.le
  have hCg : 0 ≤ Cf * gg := mul_nonneg hCf hg0'
  -- the bulk inputs
  obtain ⟨hVv, hWw, hKf, hVin, hV0, hWin, hKin, hΔ⟩ := bulk_last_in R' hVN hL8 H
    (histOut R' Nh t).g.re (histOut R' Nh t).nu.re hD hKm hmN hgre (Cf * gg) hz hy hs1 hs2 hA
    (by positivity) (by positivity) hWl hDd hKk
  -- scales
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hζ8 : ‖stZeta R' st‖ ≤ 1 / 8 := (absorb_le R' hρ0 _ _).trans hρ8
  have hZ' : stZ' R' st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  set s := fscale st.Z * R.ℓ with hsd
  set s' := fscale (stZ' R' st) * R.ℓ with hs'd
  have hs : 0 < s := mul_pos (fscale_pos hZ) hℓ
  have hs' : 0 < s' := mul_pos (fscale_pos hZ') hℓ
  have hsum : s' + s' / 4 ≤ 2 * s := by
    have hsc := scale_ok hZ hζ8 hℓ
    have e : stZ' R' st = st.Z * (1 + stZeta R' st) := rfl
    rw [hs'd, e]; rw [hsd]; linarith
  have hC : GoodCov2 (Nh + 1) (s' / 4) (LastN.stCovN R' (Nh + 1) st) := hC0
  have hss : s ^ 2 ≤ 9 / 8 * s' ^ 2 := by
    rw [hsd, hs'd, mul_pow, mul_pow, Step2.fscale_sq, Step2.fscale_sq]
    have e : stZ' R' st = st.Z * (1 + stZeta R' st) := rfl
    rw [e, norm_mul]
    have hZn : 0 < ‖st.Z‖ := norm_pos_iff.2 hZ
    have h1 : ‖1 + stZeta R' st‖ ≤ 9 / 8 := by
      refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
    have h2 : 7 / 8 ≤ ‖1 + stZeta R' st‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-stZeta R' st)
      rw [sub_neg_eq_add, norm_one, norm_neg] at this; linarith
    rw [mul_inv]
    have hR2 : 0 < R.ℓ ^ 2 := by positivity
    have : (‖st.Z‖)⁻¹ ≤ 9 / 8 * ((‖st.Z‖)⁻¹ * (‖1 + stZeta R' st‖)⁻¹) := by
      rw [← mul_assoc, mul_comm (9 / 8 : ℝ), mul_assoc]
      refine le_mul_of_one_le_right (by positivity) ?_
      rw [le_mul_inv_iff₀ (by linarith)]; linarith
    nlinarith
  have hsZ : s ^ 2 ≤ 9 / 8 * R.ℓ ^ 2 /
      ‖(lastOut R' Nh t).Z‖ := by
    have e : (lastOut R' Nh t).Z = st.Z * (1 + stZeta R' st) := rfl
    rw [hsd, mul_pow, Step2.fscale_sq, e, norm_mul]
    have hZn : 0 < ‖st.Z‖ := norm_pos_iff.2 hZ
    have h1 : ‖1 + stZeta R' st‖ ≤ 9 / 8 := by
      refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
    have h2 : 7 / 8 ≤ ‖1 + stZeta R' st‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-stZeta R' st)
      rw [sub_neg_eq_add, norm_one, norm_neg] at this; linarith
    rw [le_div_iff₀ (by positivity)]
    field_simp
    nlinarith
  -- the couplings
  set β1 := ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ with hβ1
  set β0 := ‖bt2 R P (zV b) m b μ₀ Nh‖ with hβ0
  have hflow := bt2_flow R P (zV b) (Nh := Nh + 1) (by omega) m b μ₀ (k := Nh) (by omega)
  have hBB : β0 ≤ 2 * β1 := by
    rw [hβ0, hβ1, hflow]; exact beta_step_ge htop.1 htop.2
  have hβeq : ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ₀ x)‖ = β1 := by
    have h : Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ₀ x) =
        Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (Obs2.histVO2 R' P o₀ t (Nh + 1)) := by
      unfold Obs2.betaTot2
      refine sum_congr rfl fun b' _ => ?_
      rw [Obs2.histVO2_a]
      congr 1
      exact Obs2.emb_add_cmp true _ _
    rw [h]; rfl
  set A1 := Obs2.shA2 (Obs2.histVO2 R' P o₀ t) (Nh + 1) with hA1
  have hβA : β1 ≤ A1 := by
    show ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (Obs2.histVO2 R' P o₀ t (Nh + 1))‖ ≤ A1
    exact norm_sum_le _ _
  have hβ1' : 0 ≤ β1 := norm_nonneg _
  have hA10 : 0 ≤ A1 := hβ1'.trans hβA
  have hsNh : histS R' Nh t ^ 2 ≤ 9 / 8 * s ^ 2 := by
    have h := histS_sq_le_z R' t Nh hρ0 hρ8
    have e2 : R'.ℓ = R.ℓ := rfl
    rw [e2] at h
    have e : s ^ 2 = R.ℓ ^ 2 * (zH R' t (Nh + 1))⁻¹ := by
      rw [hsd, mul_pow, Step2.fscale_sq, mul_comm]; rfl
    rw [e]; linarith
  -- the observable inputs
  have hVo : ∀ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo Obs2.wA (Nh + 1) s (lV R Nh m b μ₀ x b') ≤ ENNReal.ofReal (s ^ 2 * A1) := by
    intro b' hb'
    refine (PtCorr2.oTo_emb_add_le Obs2.wA (Nh + 1) s _ _).trans ?_
    exact vobs2_block_le' R' P (zV b) t (traj_zero_X R m b μ₀) (j := Nh + 1) (by omega) hs b' hb'
  have hWo : ∀ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo Obs2.wA (Nh + 1) s (lW R Nh m b μ₀ x b') ≤
        ENNReal.ofReal (cW * gg * histS R' Nh t ^ 2 * β0) := fun b' hb' =>
    (PtCorr2.oTo_emb_add_le Obs2.wA (Nh + 1) s _ _).trans (hW b' hb')
  have hKo : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal ((R.A / 2) ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Obs2.oTo Obs2.wA (Nh + 1) s (lK R Nh m b μ₀ x X) ≤
        ENNReal.ofReal (8 * (cK * gg * histS R' Nh t ^ 2 * β0)) := by
    intro X hX
    have hδ0 : 0 ≤ 8 * cM * R.ℓ ^ 2 * (Cf * gg) := by
      have := (Nat.cast_nonneg (α := ℝ) (Fintype.card (Mono 2))); positivity
    have h1 := oTo_fullK_le R' (Nh + 1) st (histOut R' Nh t).K o Obs2.wA Obs2.wA_ab hs hA hδ0
      (by linarith) hΔ X
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul_right (hK X hX) _
  -- the sizes
  have hcM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hcT : 1 ≤ cTauL R.ℓ Cf cW cK := by
    unfold cTauL
    have : 0 ≤ (4 * cM * R.ℓ ^ 2 + 8 * R.ℓ ^ 4) * Cf := by positivity
    linarith
  set τ := cTauL R.ℓ Cf cW cK * gg with hτd
  have hτ : 0 < τ := mul_pos (by linarith) hg0
  have hgg2 : gg ^ 2 ≤ gg := by nlinarith
  have hgg3 : gg ^ 3 ≤ gg := by nlinarith
  have hνr : |(histOut R' Nh t).nu.re| ≤ Cf * gg := (Complex.abs_re_le_norm _).trans hnu
  have hgr : (histOut R' Nh t).g.re ≤ Cf * gg := (Complex.re_le_norm _).trans hgn
  have hv : cM * R.ℓ ^ 2 * (2 * |(histOut R' Nh t).nu.re| + 2 * (Cf * gg)) +
      8 * R.ℓ ^ 4 * (histOut R' Nh t).g.re ≤ τ := by
    have h1 : cM * R.ℓ ^ 2 * (2 * |(histOut R' Nh t).nu.re| + 2 * (Cf * gg)) ≤
        cM * R.ℓ ^ 2 * (4 * (Cf * gg)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 8 * R.ℓ ^ 4 * (histOut R' Nh t).g.re ≤ 8 * R.ℓ ^ 4 * (Cf * gg) :=
      mul_le_mul_of_nonneg_left hgr (by positivity)
    have h3 : cM * R.ℓ ^ 2 * (4 * (Cf * gg)) + 8 * R.ℓ ^ 4 * (Cf * gg) ≤ τ := by
      rw [hτd]; unfold cTauL
      have : 0 ≤ (10 * Cf + 9 / 4 * cW + 18 * cK + 1) * gg := by positivity
      nlinarith
    linarith
  -- locality and the bulk parts of the full inputs
  have hloc : PtCorr2.ObsLocInv P (Nh + 1) o :=
    obsLocInv_hist R' P o₀ (obsLocInv_init .two (zV b) P) t (Nh + 1)
      fun i hi => hist_validL R' hV hVL t i (by omega)
  have hOL := olocS_last R' P (histOut R' Nh t).g.re (histOut R' Nh t).nu.re hVN H hD hKm hloc
  have eV : Obs2.bulkF (lV R Nh m b μ₀ x) =
      stVf R' (Nh + 1) st (histOut R' Nh t).g.re (histOut R' Nh t).nu.re :=
    Obs2.bulkF_fullV R' (Nh + 1) st _ _ ho
  have eW : Obs2.bulkF (lW R Nh m b μ₀ x) = st.Wl + (histOut R' Nh t).D := Obs2.bulkF_fullW st _ ho
  have eK : Obs2.bulkF (lK R Nh m b μ₀ x) =
      Kflat (Nh + 1) (stDelta R' (Nh + 1) st) (histOut R' Nh t).K :=
    Obs2.bulkF_fullK R' (Nh + 1) st _ ho
  set w := cW * gg * histS R' Nh t ^ 2 * β0 with hwd
  have hw0 : 0 ≤ w := by positivity
  have hwA : w ≤ 9 / 4 * cW * gg * (s ^ 2 * A1) := by
    have h1 : histS R' Nh t ^ 2 * β0 ≤ 9 / 8 * s ^ 2 * (2 * A1) :=
      mul_le_mul hsNh (hBB.trans (by linarith)) (norm_nonneg _) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hcW hg0')
    rw [hwd]; nlinarith
  set kk := cK * gg * histS R' Nh t ^ 2 * β0 with hkkd
  have hkA : 8 * kk ≤ 18 * cK * gg * (s ^ 2 * A1) := by
    have h1 : histS R' Nh t ^ 2 * β0 ≤ 9 / 8 * s ^ 2 * (2 * A1) :=
      mul_le_mul hsNh (hBB.trans (by linarith)) (norm_nonneg _) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hcK hg0')
    rw [hkkd]; nlinarith
  -- the estimate for every `η > 0`
  have hmain : ∀ η : ℝ, 0 < η →
      s' ^ 2 * ‖Suscept.c2 ((finG P (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x)
          (lW R Nh m b μ₀ x) (lK R Nh m b μ₀ x) : SA .two (Lam 2 L N)).a) +
        ∑ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
          Suscept.c2 ((Obs2.VpO P (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x)
            (lK R Nh m b μ₀ x) b' : SA .two (Lam 2 L N)).a)‖ ≤
        cJet L * (cRho L + 4 / r₀ ^ 2) * τ * (s ^ 2 * (A1 + η)) ∧
      ‖ε ((finG P (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x)
          (lW R Nh m b μ₀ x) (lK R Nh m b μ₀ x) : SA .two (Lam 2 L N)).a)‖ ≤
        cJet L * (cRho L + 4 / r₀ ^ 2) * τ * (s ^ 2 * (A1 + η)) := by
    intro η hη
    set M := s ^ 2 * (A1 + η) with hMd
    have hM : 0 < M := mul_pos (by positivity) (by linarith)
    have hAM : s ^ 2 * A1 ≤ M := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hτM : τ * (s ^ 2 * A1) ≤ τ * M := mul_le_mul_of_nonneg_left hAM hτ.le
    have hcτ1 : 9 / 4 * cW * gg ≤ τ := by
      rw [hτd]; unfold cTauL
      have : 0 ≤ ((4 * cM * R.ℓ ^ 2 + 8 * R.ℓ ^ 4) * Cf + 10 * Cf + 18 * cK + 1) * gg := by
        positivity
      nlinarith
    have hcτ2 : 18 * cK * gg ≤ τ := by
      rw [hτd]; unfold cTauL
      have : 0 ≤ ((4 * cM * R.ℓ ^ 2 + 8 * R.ℓ ^ 4) * Cf + 10 * Cf + 9 / 4 * cW + 1) * gg := by
        positivity
      nlinarith
    have hsA : 0 ≤ s ^ 2 * A1 := by positivity
    have hwτ : w ≤ τ * M := hwA.trans ((mul_le_mul_of_nonneg_right hcτ1 hsA).trans hτM)
    have hkτ : 8 * kk ≤ τ * M / r₀ := by
      refine hkA.trans ((mul_le_mul_of_nonneg_right hcτ2 hsA).trans (hτM.trans ?_))
      rw [le_div_iff₀ hr₀]
      exact mul_le_of_le_one_right (mul_nonneg hτ.le hM.le) hr₀1
    have hτ2 : 2 * (Cf * gg) ≤ τ := by
      rw [hτd]; unfold cTauL
      have : 0 ≤ ((4 * cM * R.ℓ ^ 2 + 8 * R.ℓ ^ 4) * Cf + 9 / 4 * cW + 18 * cK + 1) * gg := by
        positivity
      nlinarith
    have hτ8 : 8 * (Cf * gg) ≤ τ := by
      rw [hτd]; unfold cTauL
      have : 0 ≤ ((4 * cM * R.ℓ ^ 2 + 8 * R.ℓ ^ 4) * Cf + 9 / 4 * cW + 18 * cK + 1) * gg := by
        positivity
      nlinarith
    have hWτ : Cf * gg ^ 2 + Cf * gg ^ 2 ≤ τ := by
      have := mul_le_mul_of_nonneg_left hgg2 hCf; linarith
    have hKτ : 8 * (Cf * gg ^ 3) ≤ τ := by
      have := mul_le_mul_of_nonneg_left hgg3 hCf; linarith
    refine hJ N (Nh + 1) (by omega) hLp s s' (s' / 4) hs hs' (by positivity) hsum
      (LastN.stCovN R' (Nh + 1) st) hC P (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x) (lK R Nh m b μ₀ x)
      (by rw [eV]; exact hVin) (by rw [eW]; exact hWin) (by rw [eV]; exact hV0)
      (by rw [eK]; exact hKin)
      (fun b' => Obs2.cmpIn_of_osub (hOL.hV b')) (fun b' => Obs2.cmpIn_of_osub (hOL.hW b'))
      (fun X hX => Obs2.cmpIn_of_osub (hOL.hK X hX)) τ M w hτ hs5 hM hw0 hwτ
      (by rw [eV]; exact hVv.trans (ENNReal.ofReal_le_ofReal hv))
      (by rw [eW]; exact hWw.trans (ENNReal.ofReal_le_ofReal hWτ))
      (by rw [eK]; exact hKf.trans (ENNReal.ofReal_le_ofReal hKτ))
      (fun b' hb' => (hVo b' hb').trans (ENNReal.ofReal_le_ofReal hAM)) hWo
      (fun X hX => (hKo X hX).trans (ENNReal.ofReal_le_ofReal hkτ)) hs3 hs4
  -- `K_N(Λ)` through `F_N`
  have hVc : FamCovG (Nh + 1)
      (stVf R' (Nh + 1) st (histOut R' Nh t).g.re (histOut R' Nh t).nu.re) := by
    have h : stVf R' (Nh + 1) st (histOut R' Nh t).g.re (histOut R' Nh t).nu.re ∈
        BSub (L := L) (N := N) (Nh + 1) := by
      rw [stVf_eq_kap]
      exact VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hjN _
    exact h.2.1
  have hWc : FamCovG (Nh + 1) (st.Wl + (histOut R' Nh t).D) := (add_mem H.hWl hD).2.1
  obtain ⟨-, hc2F, heF⟩ := finO_last_TI R' P (Nh + 1) st (histOut R' Nh t).g.re
    (histOut R' Nh t).nu.re (histOut R' Nh t).D (histOut R' Nh t).K o (by omega) ho hCt hVc hWc
  have ec2 : Suscept.c2 ((zKN R Nh m b μ₀ x : Obs.OE .two (Lam 2 L N)) : Obs.SA .two (Lam 2 L N)).a =
      Suscept.c2 ((finG P (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x)
          (lW R Nh m b μ₀ x) (lK R Nh m b μ₀ x) : SA .two (Lam 2 L N)).a) +
        ∑ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
          Suscept.c2 ((Obs2.VpO P (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x)
            (lK R Nh m b μ₀ x) b' : SA .two (Lam 2 L N)).a) := by
    have hm : ∑ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
        mass2 ((Obs2.VpO P (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x)
          (lK R Nh m b μ₀ x) b' : SA .two (Lam 2 L N)).a) =
        -∑ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
          Suscept.c2 ((Obs2.VpO P (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x)
            (lK R Nh m b μ₀ x) b' : SA .two (Lam 2 L N)).a) := by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun _ _ => mass2_eq_neg_c2 _
    have h := hc2F
    change Suscept.c2 ((finG P (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x)
          (lW R Nh m b μ₀ x) (lK R Nh m b μ₀ x) : SA .two (Lam 2 L N)).a) =
        ∑ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
          mass2 ((Obs2.VpO P (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x)
            (lK R Nh m b μ₀ x) b' : SA .two (Lam 2 L N)).a) +
          Suscept.c2 ((zKN R Nh m b μ₀ x : Obs.OE .two (Lam 2 L N)) :
            Obs.SA .two (Lam 2 L N)).a at h
    rw [hm] at h
    linear_combination -h
  have eε : ε ((zKN R Nh m b μ₀ x : Obs.OE .two (Lam 2 L N)) : Obs.SA .two (Lam 2 L N)).a =
      ε ((finG P (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x)
          (lW R Nh m b μ₀ x) (lK R Nh m b μ₀ x) : SA .two (Lam 2 L N)).a) := heF.symm
  -- the constants
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have hc0 : 0 ≤ cJet L * (cRho L + 4 / r₀ ^ 2) := by
    have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
    have hcS : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
    have h1 : 0 ≤ cJet L := by
      unfold cJet; have := mul_nonneg hL2 (by linarith : (0 : ℝ) ≤ Q1 2); linarith
    have h2 : 0 ≤ cRho L := by
      unfold cRho
      have : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
      have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
      refine mul_nonneg hL2 ?_
      nlinarith
    exact mul_nonneg h1 (add_nonneg h2 (by positivity))
  have hcAβ : 0 ≤ cA * β1 := hA10.trans hl1
  have hcτ0 : 0 ≤ cTauL R.ℓ Cf cW cK := by linarith
  have hZn : 0 < ‖(lastOut R' Nh t).Z‖ := by
    have e : (lastOut R' Nh t).Z = stZ' R' st := rfl
    rw [e]; exact norm_pos_iff.2 hZ'
  rw [hβeq, ec2, eε]
  refine ⟨?_, ?_⟩
  · exact kA_arith_c2 (ℓ := R.ℓ) hc0 hτd hcτ0 hg0' hs' hss hl1 (fun η hη => (hmain η hη).1) hA10 hcAβ
  · exact kA_arith_eps (ℓ := R.ℓ) hc0 hτd hcτ0 hg0' hg1 hZn hsZ hl1 (fun η hη => (hmain η hη).2)
      hA10 hcAβ

/-- **`LastKRem` from the block sizes of the last step** (every point configuration). -/
theorem lastKRem_of {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Cf cW cK cA r₀ : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) (hLp : pauliL0 2 ≤ L)
    (hL8 : 2 ^ (2 + 3) + 8 * 2 < L)
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
    (hW : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      WbHc (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)
      (cW * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
        histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖))
    (hK : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      KbHc (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)
      (cK * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
        histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖))
    (htop : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → Case2TopStep R (ptsX x) (zV b) Nh m b μ₀)
    (hl1 : LastL1 R Nh m b μ₀ cA) :
    LastKRem R Nh m b μ₀ (cKAL L R.ℓ r₀ Cf cW cK cA) := fun x hx h1 hj =>
  lastKRem_x R hNh hV hVL hVN hLp hL8 hmN hG hr₀ hr₀1 hJ hcW hcK hCf hg0 hg1 hs1 hs2 hs3 hs4 hs5
    x h1 (hW x hx h1 hj) (hK x hx h1 hj) (htop x hx h1 hj) (hl1 x hx h1 hj)

end Traj

end

end Spin2
