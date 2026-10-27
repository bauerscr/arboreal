import Spin2.Pair.PairTop3
import Spin2.Pair.PairTop4
import Spin2.Pair.PairDef5a

/-!
# Top coalescence along one windowed trajectory: `|P_{1/b}[0 ↔ x] - ϑ_{N_h}²| ≤ Kϑ_{N_h}²/β_{N_h}`

For `x ≠ 0` with `j_x ≥ N_h + 1` on the `h = 0` trajectory `(b, b − m²)` in `D_ε` up to `N_h`,
from the seed size of the reduced state `oTop … dxTop` at `N_h + 1` (hypothesis `hseed`, constant
`c_K`), the master conclusions and the last-step smallness:

* `lastOneRem_x` (the body of `lastOneRem_of` at one `x`);
* `twoPt_top_pure`, `top_conv` (pure): `‖AB − M²‖ ≤ (2K_O + K_O²)‖M‖²ǧ`,
  `|P − ϑ²| ≤ ((9/4)K_P + (5/2)F)ϑ²ǧ`;
* `thetaSq_eq_varth` (`ϑ_k² = (β_k/β_ε)^{2/3}`, `ϑ_k²/β_k = ϑ_k²ǧ_k`);
* **`MasterFacts.fw_top_traj`**.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **`LastOneRem` at one point `x`** (the body of `lastOneRem_of` for a fixed `x`, no
coalescence condition). -/
theorem lastOneRem_x {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Cf cW KK : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) (hLp : pauliL0 2 ≤ L)
    (hL8 : 2 ^ (2 + 3) + 8 * 2 < L)
    (hG : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (hcW : 0 ≤ cW)
    (hg0 : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) (x : Lam 2 L N)
    (hW : WbHc (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)
      (cW * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
        histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖))
    (htop : Case2TopStep R (ptsX x) (zV b) Nh m b μ₀)
    (hsm : (Cf * (R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128) + 9 / 4 * (cBn * Q1 2 * cW) + KK) *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1 / 2)
    (hK : ‖Suscept.c2 (zKN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
        KK * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
          ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ ∧
      ‖ε (zKN R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
        KK * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ /
          ‖(lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖) :
    zP0 R Nh m b μ₀ x = 1 ∧
    ‖Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a -
        Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) * zP0 R Nh m b μ₀ x‖ ≤
      1 / 2 * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ * ‖zP0 R Nh m b μ₀ x‖ ∧
    ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      KK * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ * ‖zP0 R Nh m b μ₀ x‖ /
        ‖(lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ := by
  set R' := R.withMsq m with hR'
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set g := (t Nh).1 with hgd
  have hρ0 : 0 ≤ R'.ρ := hVL.2.2.2.2.1
  have hρ8 : R'.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hwx : ∀ x : Lam 2 L N, 0 ≤ cW * g * histS R' Nh t ^ 2 * ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖ :=
    fun x => mul_nonneg (mul_nonneg (mul_nonneg hcW hg0) (sq_nonneg _)) (norm_nonneg _)
  set B0 := ‖bt2 R (ptsX x) (zV b) m b μ₀ Nh‖ with hB0
  set w := cW * g * histS R' Nh t ^ 2 * B0 with hwd
  obtain ⟨hP0, hb2, he⟩ := lastOne_traj R hNh hV hVL hVN hLp hL8 hG x (hwx x) hW
  obtain ⟨hk1, hk2⟩ := hK
  have hβeq : Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ₀ x) =
      Obs2.betaTot2 (L := L) (N := N) (Nh + 1)
        (Obs2.histVO2 R' (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) t (Nh + 1)) := by
    unfold Obs2.betaTot2
    refine sum_congr rfl fun b' _ => ?_
    rw [Obs2.histVO2_a]
    congr 1
    exact Obs2.emb_add_cmp true _ _
  have eB : ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1)
      (Obs2.histVO2 R' (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x)) t (Nh + 1))‖ =
      ‖bt2 R (ptsX x) (zV b) m b μ₀ (Nh + 1)‖ := rfl
  set β := ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ with hβd
  have eβ : β = ‖bt2 R (ptsX x) (zV b) m b μ₀ (Nh + 1)‖ := by rw [hβd, hβeq, eB]
  have hflow := bt2_flow R (ptsX x) (zV b) (Nh := Nh + 1) (by omega) m b μ₀ (k := Nh) (by omega)
  have hBB : B0 ≤ 2 * β := by
    rw [hB0, eβ, hflow]; exact beta_step_ge htop.1 htop.2
  have hZp : 0 < zH R' t (Nh + 1) := zH_pos R' hρ0 hρ8 t (Nh + 1)
  have hS : histS R' Nh t ^ 2 ≤ 9 / 8 * R.ℓ ^ 2 * (zH R' t (Nh + 1))⁻¹ :=
    histS_sq_le_z R' t Nh hρ0 hρ8
  have hs1 : (histS R' (Nh + 1) t)⁻¹ ^ 2 = zH R' t (Nh + 1) / R.ℓ ^ 2 := by
    have hℓ : 0 < R.ℓ := Fact.out
    show (fscale (rawHist R' (Nh + 1) t).Z * R'.ℓ)⁻¹ ^ 2 = ‖(rawHist R' (Nh + 1) t).Z‖ / R.ℓ ^ 2
    rw [inv_pow, mul_pow, Step2.fscale_sq, show R'.ℓ = R.ℓ from rfl]
    have : 0 < ‖(rawHist R' (Nh + 1) t).Z‖ := hZp
    field_simp
  have hwS : cBn * (Q1 2 * w) * (histS R' (Nh + 1) t)⁻¹ ^ 2 ≤
      9 / 4 * (cBn * Q1 2 * cW) * g * β := by
    have hℓ : 0 < R.ℓ := Fact.out
    have hQ : 0 ≤ Q1 2 := by have := one_le_Q1 (d := 2) (by norm_num); linarith
    have hcB : (0 : ℝ) ≤ cBn := Nat.cast_nonneg _
    have hK0 : 0 ≤ cBn * Q1 2 * cW * g := mul_nonneg (mul_nonneg (mul_nonneg hcB hQ) hcW) hg0
    rw [hs1, hwd]
    have h1 : histS R' Nh t ^ 2 * zH R' t (Nh + 1) / R.ℓ ^ 2 ≤ 9 / 8 := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hS hZp.le
      rw [show 9 / 8 * R.ℓ ^ 2 * (zH R' t (Nh + 1))⁻¹ * zH R' t (Nh + 1) = 9 / 8 * R.ℓ ^ 2 by
        field_simp] at this
      linarith
    calc cBn * (Q1 2 * (cW * g * histS R' Nh t ^ 2 * B0)) * (zH R' t (Nh + 1) / R.ℓ ^ 2)
        = (cBn * Q1 2 * cW * g) * B0 * (histS R' Nh t ^ 2 * zH R' t (Nh + 1) / R.ℓ ^ 2) := by ring
      _ ≤ (cBn * Q1 2 * cW * g) * (2 * β) * (9 / 8) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hBB hK0) h1
            (div_nonneg (mul_nonneg (sq_nonneg _) hZp.le) (sq_nonneg _))
            (mul_nonneg hK0 (by linarith [norm_nonneg (Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x))]))
      _ = 9 / 4 * (cBn * Q1 2 * cW) * g * β := by ring
  refine ⟨hP0, ?_⟩
  simp only [hP0, mul_one, norm_one]
  refine ⟨?_, by rw [he]; exact hk2⟩
  have hb3 := hb2.trans (add_le_add (add_le_add le_rfl hwS) hk1)
  have hβ0 : 0 ≤ β := norm_nonneg _
  have := mul_le_mul_of_nonneg_right hsm hβ0
  calc _ ≤ _ := hb3
    _ = (Cf * (R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128) + 9 / 4 * (cBn * Q1 2 * cW) + KK) * g * β := by ring
    _ ≤ 1 / 2 * β := this

end Traj

/-- `‖AB − M²‖ ≤ (2K + K²)‖M‖²g` from `‖A − M‖, ‖B − M‖ ≤ K‖M‖g`, `0 ≤ g ≤ 1` (pure). -/
theorem twoPt_top_pure {A B Mc : ℂ} {K g : ℝ} (hK : 0 ≤ K) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hA : ‖A - Mc‖ ≤ K * ‖Mc‖ * g) (hB : ‖B - Mc‖ ≤ K * ‖Mc‖ * g) :
    ‖A * B - Mc ^ 2‖ ≤ (2 * K + K ^ 2) * ‖Mc‖ ^ 2 * g := by
  have e : A * B - Mc ^ 2 = (A - Mc) * B + Mc * (B - Mc) := by ring
  rw [e]
  have hBn : ‖B‖ ≤ ‖Mc‖ + K * ‖Mc‖ * g := by
    have := norm_le_insert' B Mc; linarith
  have hM0 := norm_nonneg Mc
  have h1 : ‖(A - Mc) * B‖ ≤ K * ‖Mc‖ * g * (‖Mc‖ + K * ‖Mc‖ * g) := by
    rw [norm_mul]; exact mul_le_mul hA hBn (norm_nonneg _) (by positivity)
  have h2 : ‖Mc * (B - Mc)‖ ≤ ‖Mc‖ * (K * ‖Mc‖ * g) := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hB hM0
  have h3 : K * ‖Mc‖ * g * (K * ‖Mc‖ * g) ≤ K ^ 2 * ‖Mc‖ ^ 2 * g := by
    have : g * g ≤ g := mul_le_of_le_one_left hg0 hg1
    have h0 : 0 ≤ K ^ 2 * ‖Mc‖ ^ 2 := by positivity
    have e' : K * ‖Mc‖ * g * (K * ‖Mc‖ * g) = K ^ 2 * ‖Mc‖ ^ 2 * (g * g) := by ring
    rw [e']; exact mul_le_mul_of_nonneg_left this h0
  calc ‖(A - Mc) * B + Mc * (B - Mc)‖ ≤ ‖(A - Mc) * B‖ + ‖Mc * (B - Mc)‖ := norm_add_le _ _
    _ ≤ K * ‖Mc‖ * g * (‖Mc‖ + K * ‖Mc‖ * g) + ‖Mc‖ * (K * ‖Mc‖ * g) := add_le_add h1 h2
    _ = 2 * K * ‖Mc‖ ^ 2 * g + K * ‖Mc‖ * g * (K * ‖Mc‖ * g) := by ring
    _ ≤ 2 * K * ‖Mc‖ ^ 2 * g + K ^ 2 * ‖Mc‖ ^ 2 * g := by linarith
    _ = (2 * K + K ^ 2) * ‖Mc‖ ^ 2 * g := by ring

/-- **From `M` to `ϑ`** (pure): `‖P − M²‖ ≤ K‖M‖²g`, `‖M − ϑ‖ ≤ Fϑg`, `Fg ≤ ½` give
`|P − ϑ²| ≤ ((9/4)K + (5/2)F)ϑ²g`. -/
theorem top_conv {P : ℝ} {Mc : ℂ} {v g K F : ℝ} (hv : 0 ≤ v) (hg : 0 ≤ g) (hK : 0 ≤ K)
    (hF : 0 ≤ F) (hFg : F * g ≤ 1 / 2) (hM : ‖Mc - (v : ℂ)‖ ≤ F * v * g)
    (hP : ‖((P : ℝ) : ℂ) - Mc ^ 2‖ ≤ K * ‖Mc‖ ^ 2 * g) :
    |P - v ^ 2| ≤ (9 / 4 * K + 5 / 2 * F) * v ^ 2 * g := by
  have hvn : ‖(v : ℂ)‖ = v := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
  have hFvg : F * v * g ≤ v / 2 := by
    have := mul_le_mul_of_nonneg_right hFg hv
    nlinarith
  have hMn : ‖Mc‖ ≤ 3 / 2 * v := by
    have := norm_le_insert' Mc (v : ℂ); rw [hvn] at this; linarith
  have hMn2 : ‖Mc‖ ^ 2 ≤ 9 / 4 * v ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hMn 2
    nlinarith
  have hsum : ‖Mc + (v : ℂ)‖ ≤ 5 / 2 * v := by
    have := norm_add_le Mc (v : ℂ); rw [hvn] at this; linarith
  have e : |P - v ^ 2| = ‖((P : ℝ) : ℂ) - ((v : ℝ) : ℂ) ^ 2‖ := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [e]
  have e2 : ((P : ℝ) : ℂ) - ((v : ℝ) : ℂ) ^ 2 =
      (((P : ℝ) : ℂ) - Mc ^ 2) + (Mc - (v : ℂ)) * (Mc + (v : ℂ)) := by ring
  rw [e2]
  have h1 : ‖((P : ℝ) : ℂ) - Mc ^ 2‖ ≤ K * (9 / 4 * v ^ 2) * g :=
    hP.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMn2 hK) hg)
  have h2 : ‖(Mc - (v : ℂ)) * (Mc + (v : ℂ))‖ ≤ F * v * g * (5 / 2 * v) := by
    rw [norm_mul]; exact mul_le_mul hM hsum (norm_nonneg _) (by positivity)
  calc _ ≤ ‖((P : ℝ) : ℂ) - Mc ^ 2‖ + ‖(Mc - (v : ℂ)) * (Mc + (v : ℂ))‖ := norm_add_le _ _
    _ ≤ K * (9 / 4 * v ^ 2) * g + F * v * g * (5 / 2 * v) := add_le_add h1 h2
    _ = (9 / 4 * K + 5 / 2 * F) * v ^ 2 * g := by ring

section Traj2

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `ϑ_k² = (β_k/β_ε)^{2/3}` and `ϑ_k²/β_k = ϑ_k²ǧ_k`. -/
theorem thetaSq_eq_varth {m b μ₀ : ℝ} (hb : 0 < b) {k : ℕ}
    (hg : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) :
    thetaSq R m b μ₀ k = varthJ R m b μ₀ k ^ 2 ∧
      thetaSq R m b μ₀ k / betaJ R m b μ₀ k =
        varthJ R m b μ₀ k ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 := by
  have hq : 0 ≤ b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 := (div_pos hb hg).le
  have h1 : thetaSq R m b μ₀ k = varthJ R m b μ₀ k ^ 2 := by
    unfold thetaSq varthJ betaJ
    have e : 1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / (1 / b) =
        b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 := by field_simp
    rw [e]
    set q := b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1
    rw [← Real.rpow_mul_natCast hq]
    norm_num
  refine ⟨h1, ?_⟩
  rw [h1]
  unfold betaJ
  field_simp

end Traj2

end

end Spin2
