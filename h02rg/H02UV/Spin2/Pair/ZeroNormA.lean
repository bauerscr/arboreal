import Spin2.Pair.ZeroNorm
import PtCorr2.Last.LastObsA
import PtCorr2.Zero.Flow

/-!
# PR6 items (a), (e) of `PairZeroRemW`: `P₀ ≠ 0` and the zero-mode constant

Pair observable `z̃_0z̃_x`, `F = F_N` (`zFin`), `P₀ = ∏_B(1 + ε𝒲_N(B)_∅)` (`zP0`, the block
factors of the *observable* last step, `𝒲_N = S - Loc S`), `c = t_raw/|Λ|` (`zCc`),
`Z = Z_N` of the bulk final-scale object `lastOut`, `ǧ = ǧ_{N_h}`.

* **`p0_last_le`** (any history): `GlueOut` gives `|P₀ - 1| ≤ L²w e^{L²w}`,
  `w = (1 + L²)C_fǧ²`. The `∅`-part of `𝒲_N(B)` is `Step2.Wp = S(B) - Loc_{Λ,B}S(Λ)` (`bulk_WpO`),
  `|εS(B)| ≤ C_fǧ²` (`GlueOut`: `S(B)` is the `𝒲_N(B)` of `lastOut`) and
  `|ε Loc_{Λ,B}S(Λ)| ≤ L²C_fǧ²` (`PtCorr2.eps_LS_le`). Note: `P₀` is **not** `P0Fin (lastOut)`
  (the bulk last step `rawStepN` keeps `S(B)` without `Loc`); both are `1 + O(ǧ²)`.
* **`zP0_ne_of`**: `L²(1 + L²)C_fǧ² ≤ ¼` gives `|P₀ - 1| ≤ ½`, so `P₀ ≠ 0` and `|P₀| ≥ ½`
  (item (a)).
* **`zCc_ge`**: from `|m²Z t_raw - 1| ≤ K m²L^{2N}` (`ZeroTOk`, `PtCorr2.lastOut_zeroT`) and the
  **mass window** `K m² L^{2N} ≤ ½`: `|c| ≥ 1/(2m²|Z|L^{2N})`.
* Named input **`LastOneRem K_A`** (the one-point activity of the last step, open): item (b) of
  `PairZeroRemW` and `‖εF_a‖ ≤ K_A‖β_{a,N-1}‖‖P₀‖/|Z|` (the natural size: the tadpole of the
  vertex `β ψ̄_aψ_a` against `C_N`, `C_N(a,a) ∝ ℓ²/|Z_N|`).
* Named input **`PairZeroRemAB e₁ e₂`**: items (c), (d) of `PairZeroRemW` (the `w_{ab} > 0` layer).
* **`pairZeroRemW_of_A`**: (a) from `zP0_ne_of`, (b) and the size of `εF_a` from `LastOneRem`,
  (c), (d) from `PairZeroRemAB`, and (e) from `zCc_ge` and the second **mass window**
  `8K_A m²L^{2N} ≤ 1`: `‖εF_a‖ ≤ K_A‖β‖‖P₀‖/|Z| ≤ ¼·|β||P₀|/(2m²|Z|L^{2N}) ≤ ¼|c||β||P₀|`.

**Mass window.** Item (e) compares the one-point activity `≈ ℓ²|β|/|Z|` with the zero-mode
vertex `|c||β| ≈ |β|/(m²|Z|L^{2N})`; at the top of `mRange` (`m²L^{2N} = L²`) the zero mode is
not dominant and (e) cannot hold from norm bounds. Hence the restriction `m² ≤ c₀L^{-2N}`
(`c₀ = min(1/(2K), 1/(8K_A))`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA

variable {L N : ℕ} [NeZero L]

/-- **`|P₀ - 1|` of the observable last step** (any history). -/
theorem p0_last_le (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ}
    (hNh : Nh + 2 = N) (hρ0 : 0 ≤ R.ρ) (hρ1 : R.ρ < 1) (P : Obs2.ObsPts 2 L N)
    (V : Obs2.OCoup .two) {Cf : ℝ} (hCf : 0 ≤ Cf) (t : Hist.Seq (Xs R))
    (hG : GlueOut R Nh Cf t) :
    ‖PtCorr2.blkP0 (blocks (Nh + 1) (univ : Finset (Lam 2 L N)))
        (Obs2.WpO P (Nh + 1) (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
          (Obs2.fullV R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
            (Obs2.obsHist R P (Obs2.obsInit .two V P) (Nh + 1) t))
          (Obs2.fullW (histOut R Nh t).st (histOut R Nh t).D
            (Obs2.obsHist R P (Obs2.obsInit .two V P) (Nh + 1) t))) - 1‖ ≤
      (L : ℝ) ^ 2 * ((1 + (L : ℝ) ^ 2) * (Cf * (t Nh).1 ^ 2)) *
        Real.exp ((L : ℝ) ^ 2 * ((1 + (L : ℝ) ^ 2) * (Cf * (t Nh).1 ^ 2))) := by
  have hℓ : 0 < R.ℓ := Fact.out
  set o := Obs2.obsHist R P (Obs2.obsInit .two V P) (Nh + 1) t with hod
  set st := (histOut R Nh t).st with hst
  have ho : o.IsObs := Obs2.obsHist_isObs R P _ (Obs2.obsInit_isObs .two V P) (Nh + 1) t
  set C := LastN.stCovN R (Nh + 1) st
  set w := Cf * (t Nh).1 ^ 2 with hw
  have hw0 : 0 ≤ w := by positivity
  obtain ⟨-, -, -, -, -, hB, -⟩ := hG.2
  have hZ : (lastOut R Nh t).Z ≠ 0 := lastOut_Z_ne R hρ0 hρ1 Nh t
  have hh : 0 < fscale (lastOut R Nh t).Z * R.ℓ := mul_pos (fscale_pos hZ) hℓ
  have hL0 : (0 : ℝ) < (L : ℝ) ^ (Nh + 1 + 1) :=
    pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hS : ∀ b ∈ blockIdx (d := 2) (L := L) (N := N) (Nh + 1),
      ‖ε (Sb (Nh + 1) C (stVf R (Nh + 1) st (histOut R Nh t).g.re (histOut R Nh t).nu.re)
        (st.Wl + (histOut R Nh t).D) b : Alg 2 L N)‖ ≤ w := fun b hb =>
    (abs_eps_le (E := Dir 2) (p := pPhi 2) hL0 hh _).trans (toReal_le_of hw0 (hB b hb).2.2)
  have hx : ∀ b ∈ blocks (Nh + 1) (univ : Finset (Lam 2 L N)),
      ‖ε (((Obs2.WpO P (Nh + 1) C (Obs2.fullV R (Nh + 1) st (histOut R Nh t).g.re
        (histOut R Nh t).nu.re o) (Obs2.fullW st (histOut R Nh t).D o)) b :
          SA .two (Lam 2 L N)).e)‖ ≤ (1 + (L : ℝ) ^ 2) * w := by
    intro b hb
    have e : ((Obs2.WpO P (Nh + 1) C (Obs2.fullV R (Nh + 1) st (histOut R Nh t).g.re
        (histOut R Nh t).nu.re o) (Obs2.fullW st (histOut R Nh t).D o)) b :
          SA .two (Lam 2 L N)).e =
        ((Obs.bulk (Obs2.WpO P (Nh + 1) C (Obs2.fullV R (Nh + 1) st (histOut R Nh t).g.re
          (histOut R Nh t).nu.re o) (Obs2.fullW st (histOut R Nh t).D o) b) :
            EvR (Lam 2 L N)) : Alg 2 L N) := rfl
    rw [e, Obs2.bulk_WpO, Obs2.bulkF_fullV R _ _ _ _ ho, Obs2.bulkF_fullW _ _ ho]
    exact PtCorr2.eps_Wp_last_le (Nh + 1) C _ _ (by omega) hw0 hS b hb
  have hM : (blocks (Nh + 1) (univ : Finset (Lam 2 L N))).card ≤ L ^ 2 :=
    LastN.card_blockIdx_last (by omega)
  have h := (prod_bounds _ _ (by positivity) hM hx).1
  unfold PtCorr2.blkP0
  push_cast at h
  exact h

/-- `exp(1/4) < 2`. -/
theorem exp_quarter_lt_two : Real.exp (1 / 4) < 2 := by
  have h4 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_lt_d9
  by_contra hc
  replace hc := not_lt.1 hc
  have : (2 : ℝ) ^ 4 ≤ Real.exp (1 / 4) ^ 4 := pow_le_pow_left₀ (by norm_num) hc 4
  rw [h4] at this
  norm_num at this
  linarith

/-- `|P₀ - 1| ≤ X e^X` with `X ≤ ¼` gives `|P₀ - 1| ≤ ½`, so `P₀ ≠ 0`, `|P₀| ≥ ½`. -/
theorem p0_ne_of {P0 : ℂ} {X : ℝ} (_hX0 : 0 ≤ X) (hX : X ≤ 1 / 4)
    (h : ‖P0 - 1‖ ≤ X * Real.exp X) : P0 ≠ 0 ∧ 1 / 2 ≤ ‖P0‖ := by
  have hE : Real.exp X ≤ Real.exp (1 / 4) := Real.exp_le_exp.2 hX
  have h2 := exp_quarter_lt_two
  have h1 : ‖P0 - 1‖ ≤ 1 / 2 := by
    refine h.trans ?_
    have : X * Real.exp X ≤ 1 / 4 * 2 :=
      mul_le_mul hX (hE.trans h2.le) (Real.exp_pos _).le (by norm_num)
    linarith
  have h3 : 1 / 2 ≤ ‖P0‖ := by
    have e : (1 : ℂ) = P0 - (P0 - 1) := by ring
    have := norm_sub_le P0 (P0 - 1)
    rw [← e, norm_one] at this
    linarith
  exact ⟨fun h0 => by rw [h0, norm_zero] at h3; linarith, h3⟩

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **Item (a)**: `P₀ ≠ 0`, `|P₀| ≥ ½` from `GlueOut` and `L²(1 + L²)C_fǧ_{N_h}² ≤ ¼`. -/
theorem zP0_ne_of {Nh : ℕ} (hNh : Nh + 2 = N) (m b μ₀ : ℝ) (hρ0 : 0 ≤ R.ρ) (hρ1 : R.ρ < 1)
    {Cf : ℝ} (hCf : 0 ≤ Cf)
    (hG : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (hsm : (L : ℝ) ^ 2 * ((1 + (L : ℝ) ^ 2) *
      (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ^ 2)) ≤ 1 / 4) (x : Lam 2 L N) :
    zP0 R Nh m b μ₀ x ≠ 0 ∧ 1 / 2 ≤ ‖zP0 R Nh m b μ₀ x‖ := by
  have h := p0_last_le (R.withMsq m) hNh hρ0 hρ1 (ptsX x) (zV b) hCf _ hG
  exact p0_ne_of (by positivity) hsm h

/-- **The zero-mode constant from below** (mass window `K m²L^{2N} ≤ ½`). -/
theorem zCc_ge {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ} (hm0 : 0 < m) (b μ₀ : ℝ) {Kt : ℝ}
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2)
    (hZ : (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z ≠ 0) :
    1 / (2 * m * ‖(lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ *
      (L : ℝ) ^ (2 * N)) ≤ ‖zCc R Nh m b μ₀‖ := by
  set Z := (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z
  have htr := norm_tr_ge hm0 hZ (hK.trans hmT)
  have hcard : ‖(Fintype.card (Lam 2 L N) : ℂ)‖ = (L : ℝ) ^ (2 * N) := by
    rw [card_lam_two_eq (L := L) hNh, norm_pow, Complex.norm_natCast, ← hNh]
  have hLp : 0 < (L : ℝ) ^ (2 * N) :=
    pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  rw [zCc, norm_div, hcard]
  have e : 1 / (2 * m * ‖Z‖ * (L : ℝ) ^ (2 * N)) = 1 / (2 * m * ‖Z‖) / (L : ℝ) ^ (2 * N) := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right htr hLp.le

/-- **Named input (PR6, the one-point activity of the last step).** Item (b) of `PairZeroRemW`
and the size of the constant `εF_a`, relative to `|β_{a,N-1}||P₀|/|Z_N|`. -/
def LastOneRem (Nh : ℕ) (m b μ₀ : ℝ) (KA : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a -
        Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) * zP0 R Nh m b μ₀ x‖ ≤
      1 / 2 * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ * ‖zP0 R Nh m b μ₀ x‖ ∧
    ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      KA * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ * ‖zP0 R Nh m b μ₀ x‖ /
        ‖(lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖

/-- **Named input (PR6, the `σ_aσ_b` items (c), (d) of `PairZeroRemW`).** -/
def PairZeroRemAB (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (e1 e2 : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖Suscept.c2 (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab -
        rRN R Nh m b μ₀ oR x * zP0 R Nh m b μ₀ x‖ ≤
      e1 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
        ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ * ‖zP0 R Nh m b μ₀ x‖ ∧
    ‖ε (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
      e2 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
        (‖zCc R Nh m b μ₀‖ * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ *
          ‖zP0 R Nh m b μ₀ x‖)

end Traj

end

end Spin2
