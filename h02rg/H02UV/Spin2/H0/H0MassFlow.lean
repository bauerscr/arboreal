import Spin2.H0.H0Factors
import PtCorr2.Zero.WardNeg2
import Spin2.H0.H0SlackReq

/-!
# Route (a1): the quantitative last-two-step mass flow at the window ends

Along a trajectory in `D_ε` up to `N_h` (any sign of `h`) write `ǧ = ǧ_{N_h}`, `μ = μ_{N_h}`,
`V = |Λ| = L^{2N}`, `Z_N = z > 0` (real, `Zr_real_pos`), `ã = aFin`, `t_raw = zmRaw`, `k⁰ = k0Fin`,
and the normalised quantities

  `â = |Λ|ã/Z_N`, `w = m²Z_Nt_raw`, `n = m²|Λ|U = m²|Λ|(1+k⁰) + âw`.

The inputs (all in the master construction):
* `|L^{2N}ν_N/Z_N − L⁴μ| ≤ cNuLast·ǧ` (`GlueNuD`, the sharp relation through the last two steps,
  `Step2.glue_hist_nu`);
* `|â − L^{2N}ν_N/Z_N| ≤ e_a`, `|L^{2N}ν_N/Z_N| ≤ C_fǧ`, `|k⁰| ≤ κ₀` (`ZeroModeOut`);
* `|w − 1| ≤ K_T m²|Λ|` (`lastOut_zeroT`);
* the dressed susceptibility with the geometric error (`suscept2_dressed_geo`): `χ = |Λ|p/(zn)`
  up to `(|Λ|/z)(c₀ + c₁|â|/|n|)`, `c₀ = 24ρ²Be^{(64/7)ρB}/L²`, `c₁ = (64/7)ρBe^{(64/7)ρB}/L²`,
  `|p − 1| ≤ κ₀ + |â|K_T`.

Hence `Re n = L⁴μ + O(slack)` and `Re χ` has the sign of `Re n` once `|L⁴μ|` exceeds the explicit
slack `h0Slack` (**`MasterCore.h0Mass`**, `H0MassEnd`): at the upper window end (`μ_{N_h} = c₁`,
`L⁴c₁ > slack`) `U ≠ 0` and `Re χ > 0`; at the lower end (`μ_{N_h} = −c₁`) `U ≠ 0` and
`Re χ < 0`. Then

* **`h0OnePtUp_of_re`**: `⟨Z_0⟩ ≠ 0`, `r ≥ 0` real and `Re χ > 0` give `H0OnePtUp` (Ward:
  `h'Re χ = r`, so `h' ≥ 0`; positivity at `h ≥ 0` makes `χ` real);
* **`h0SusceptExit_of_re`**: `Re χ < 0` at a point of the window gives `H0SusceptExit`;
* **`MasterCore.h0Ends`**: both at the window ends, with only `r ≥ 0` at `μ₊` as input.

The slack is `cNuLast·ǧ + O(C_f²L²ǧ³) + O(C_fK_Tǧ·m²|Λ|) + 2m²|Λ|(1+κ₀) + O(ρB(ǧ + m²|Λ|)²/L²)`:
with `m²|Λ| ≤ ǧ` it is `(cNuLast + 2 + O(ε))ǧ`, which is `< L⁴θǧ` for `θ = (3/4)c_μ`
(`L^{-4}cNuLast ≈ 1.09ℓ² < (3/4)c_μ ≈ 1.47ℓ²`, see Log).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-! ### The slack -/

/-- `E = L²C_fǧ²e^{L²C_fǧ²}` (`ZeroModeOut`). -/
def h0Ez (Lr Cf g : ℝ) : ℝ := Lr ^ 2 * Cf * g ^ 2 * Real.exp (Lr ^ 2 * Cf * g ^ 2)
/-- `e_a = C_fǧE + ℓ^{-2}(E + C_fǧ³)`. -/
def h0ea (Lr Cf ℓ g : ℝ) : ℝ := Cf * g * h0Ez Lr Cf g + ℓ⁻¹ ^ 2 * (h0Ez Lr Cf g + Cf * g ^ 3)
/-- `κ₀ = E + C_fǧ³` (bound of `k⁰`). -/
def h0k0 (Lr Cf g : ℝ) : ℝ := h0Ez Lr Cf g + Cf * g ^ 3
/-- `|â| ≤ C_fǧ + e_a`. -/
def h0ahi (Lr Cf ℓ g : ℝ) : ℝ := Cf * g + h0ea Lr Cf ℓ g
/-- `|n| ≤ m²|Λ|(1 + κ₀) + |â|(1 + K_Tm²|Λ|)`. -/
def h0nhi (Lr Cf ℓ KT g mV : ℝ) : ℝ := mV * (1 + h0k0 Lr Cf g) + h0ahi Lr Cf ℓ g * (1 + KT * mV)
/-- The dressing part of the slack, `π|n| + c₀|n|² + c₁|â||n|` at the upper bounds. -/
def h0Q (Lr Cf ℓ KT B ρ g mV : ℝ) : ℝ :=
  (h0k0 Lr Cf g + h0ahi Lr Cf ℓ g * KT) * h0nhi Lr Cf ℓ KT g mV +
    24 * ρ ^ 2 * B * Real.exp (64 / 7 * ρ * B) / Lr ^ 2 * h0nhi Lr Cf ℓ KT g mV ^ 2 +
    64 / 7 * ρ * B * Real.exp (64 / 7 * ρ * B) / Lr ^ 2 * h0ahi Lr Cf ℓ g * h0nhi Lr Cf ℓ KT g mV
/-- **The slack of the window ends**: `Re n` and `L⁴μ_{N_h}` differ by less, and the dressing
corrections of `Re χ` are below it. -/
def h0Slack (Lr Cf ℓ cNL KT B ρ g mV : ℝ) : ℝ :=
  cNL * g + h0ea Lr Cf ℓ g + h0ahi Lr Cf ℓ g * (KT * mV) + mV * (1 + h0k0 Lr Cf g) +
    h0Q Lr Cf ℓ KT B ρ g mV

/-- **The conclusion at one trajectory**: if `L⁴μ_{N_h}` exceeds the slack `S`, then `U ≠ 0` and
`Re χ > 0`; if it is below `−S`, then `U ≠ 0` and `Re χ < 0`. -/
def H0MassEnd {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (m b μ : ℝ) (Nh : ℕ) (S : ℝ) : Prop :=
  (S < (L : ℝ) ^ 4 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).2.1 →
    1 + uFin (Nh + 1) (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ))
        (zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ)).ζ) ≠ 0 ∧
      0 < (∑ x : Lam 2 L N, avg0 L N m b μ (psibar 0 * psi x)).re) ∧
  ((L : ℝ) ^ 4 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).2.1 < -S →
    1 + uFin (Nh + 1) (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ))
        (zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ)).ζ) ≠ 0 ∧
      (∑ x : Lam 2 L N, avg0 L N m b μ (psibar 0 * psi x)).re < 0)

/-- The error of the dressed susceptibility in normalised units (real algebra). -/
theorem h0_err_real {P Lsq V z m ρ B E2 a ah nU nn : ℝ} (hP : V = P * Lsq) (hLsq : 0 < Lsq)
    (hz : 0 < z) (hm : 0 < m) (hV : 0 < V) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (hE2 : 0 ≤ E2)
    (hnn : nn = m * V * nU) (hnn0 : 0 < nn) (ha : ah ≤ a) :
    P / z * E2 * (24 * ρ ^ 2 * B + 64 / 7 * ρ * B * (ah / V / (m * nU))) ≤
      V / z * (24 * ρ ^ 2 * B * E2 / Lsq + 64 / 7 * ρ * B * E2 / Lsq * a / nn) := by
  have hP' : P = V / Lsq := by rw [hP]; field_simp
  have hnU : 0 < nU := by
    rw [hnn] at hnn0
    exact pos_of_mul_pos_right hnn0 (mul_pos hm hV).le
  have e1 : ah / V / (m * nU) = ah / nn := by rw [hnn]; field_simp
  rw [e1, hP']
  have h1 : ah / nn ≤ a / nn := div_le_div_of_nonneg_right ha hnn0.le
  have h2 : 0 ≤ 64 / 7 * ρ * B := by positivity
  have h3 : 24 * ρ ^ 2 * B + 64 / 7 * ρ * B * (ah / nn) ≤ 24 * ρ ^ 2 * B + 64 / 7 * ρ * B * (a / nn) :=
    by linarith only [mul_le_mul_of_nonneg_left h1 h2]
  calc V / Lsq / z * E2 * (24 * ρ ^ 2 * B + 64 / 7 * ρ * B * (ah / nn))
      ≤ V / Lsq / z * E2 * (24 * ρ ^ 2 * B + 64 / 7 * ρ * B * (a / nn)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by field_simp

/-! ### The mass flow at the window ends -/

set_option maxHeartbeats 4000000 in
/-- **The last-two-step mass flow along windowed trajectories** (any sign of `h`), for given
constants `K_T` (`ZeroTK`) and `B` (`EpsZeroSmall`). -/
theorem MasterCore.h0MassAt {L : ℕ} [NeZero L] (D : MasterCore L) {KT B : ℝ} (hKT : 0 ≤ KT) (hB : 0 ≤ B)
    (hE : EpsZeroSmall Pc L D.ρ B) (hZT : ZeroTK L D.ρ KT) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = D.ℓ → R.A = D.A → R.ρ = D.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
    ∀ b μ : ℝ, 0 < b →
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ j)) →
      H0MassEnd R m b μ Nh (h0Slack L D.Cf D.ℓ (cNuLast (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.ε) KT B
        D.ρ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).1 (m * Fintype.card (Lam 2 L N))) := by
  obtain ⟨-, -, hρ, -, -, -, -, -, -, -, hCf, -, -, hρ8, hspl, H⟩ := D.hC2
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ hb hD
  obtain ⟨-, -, -, -, -, -, -, -, -, hval⟩ := H N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  obtain ⟨hV, hVL⟩ := hval m hm
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by show 0 ≤ R.ρ; rw [hRρ]; exact hρ.le
  have hρ1 : (R.withMsq m).ρ < 1 := by show R.ρ < 1; rw [hRρ]; linarith
  have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by show R.ρ ≤ 1 / 8; rw [hRρ]; exact hρ8
  have hspl' : SplitSmall (R.withMsq m).P L (R.withMsq m).ρ := by
    show SplitSmall R.P L R.ρ; rw [hP, hRρ]; exact hspl
  have hE' : EpsZeroSmall (R.withMsq m).P L (R.withMsq m).ρ B := by
    show EpsZeroSmall R.P L R.ρ B; rw [hP, hRρ]; exact hE
  have hm0 : 0 < m := hm.1
  have hL7 : 7 ≤ L := by have := D.hL49; omega
  have hℓR : (R.withMsq m).ℓ = D.ℓ := hRℓ
  have hρR : (R.withMsq m).ρ = D.ρ := hRρ
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ with ht
  set out := lastOut (R.withMsq m) Nh t with hout
  set g := (t Nh).1 with hg
  set c := (t Nh).2.1 with hc
  have hg0 : 0 ≤ g := ((hD Nh le_rfl).1).le
  -- the inputs
  obtain ⟨-, -, -, hk0, -, -, hnu, ha⟩ := (D.onePtWin R hP hi0 hRℓ hRA hRρ hN hNh hm hb hD).1
  have hnuS := D.hGN N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ hD
  have hw := hZT N (R.withMsq m) hP hρ0 (le_of_eq hρR) hm0 hm.2 Nh hNh t
  obtain ⟨z, hz, hzZ⟩ := Zr_real_pos (R.withMsq m) hρ0 hρ1 ((L : ℝ) ^ 2) b μ (Nh + 2)
  have hZz : out.Z = (z : ℂ) := hzZ
  -- the volume
  set V : ℝ := (Fintype.card (Lam 2 L N) : ℝ) with hVd
  have hVc : (Fintype.card (Lam 2 L N) : ℂ) = (V : ℂ) := by simp [hVd]
  have hVL2 : V = ((L : ℝ) ^ 2) ^ (Nh + 1) * (L : ℝ) ^ 2 := by
    have h1 := card_lam_two_eq (L := L) hNh
    have h2 : ((V : ℝ) : ℂ) = ((((L : ℝ) ^ 2) ^ (Nh + 1) * (L : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hVc, h1]; push_cast; ring
    exact_mod_cast h2
  have hVN : (L : ℝ) ^ (2 * N) = V := by rw [hVL2, ← hNh]; ring
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hV0 : 0 < V := by rw [hVL2]; positivity
  -- names
  set A := aFin (Nh + 1) out with hA
  set tr := zmRaw (R.withMsq m) (Nh + 1) out.ζ with htr
  set k0 := k0Fin (Nh + 1) out with hk0d
  set νh := (L : ℂ) ^ (2 * (Nh + 1 + 1)) * out.κ.nu / out.Z with hνh
  set ah : ℂ := (V : ℂ) * A / (z : ℂ) with hah
  set w : ℂ := (m : ℂ) * ((z : ℂ) * tr) with hw'
  set mV := m * V with hmV
  have hmV0 : 0 < mV := mul_pos hm0 hV0
  set n : ℂ := ((m * V : ℝ) : ℂ) * (1 + k0) + ah * w with hn
  set Cf := D.Cf
  set ea := h0ea L Cf D.ℓ g
  set κ0 := h0k0 L Cf g
  set ahi := h0ahi L Cf D.ℓ g
  set cNL := cNuLast (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.ε
  have hUeq : 1 + uFin (Nh + 1) out tr = 1 + (k0 + A * tr) := rfl
  -- the bounds in normalised form
  have hEz0 : 0 ≤ h0Ez L Cf g := by unfold h0Ez; have := Real.exp_pos ((L : ℝ) ^ 2 * Cf * g ^ 2); positivity
  have hea0 : 0 ≤ ea := by
    show 0 ≤ h0ea L Cf D.ℓ g; unfold h0ea; positivity
  have hκ00 : 0 ≤ κ0 := by show 0 ≤ h0k0 L Cf g; unfold h0k0; positivity
  have hahi0 : 0 ≤ ahi := by show 0 ≤ h0ahi L Cf D.ℓ g; unfold h0ahi; positivity
  have b_a : ‖ah - νh‖ ≤ ea := by
    have e : ah = (Fintype.card (Lam 2 L N) : ℂ) * A / out.Z := by rw [hVc, hZz]
    rw [e]
    have : ‖(Fintype.card (Lam 2 L N) : ℂ) * aFin (Nh + 1) out / out.Z - νh‖ ≤
        Cf * g * h0Ez L Cf g + (R.withMsq m).ℓ⁻¹ ^ 2 * (h0Ez L Cf g + Cf * g ^ 3) := ha
    rwa [hℓR] at this
  have b_s : ‖νh - (((L : ℝ) ^ 4 * c : ℝ) : ℂ)‖ ≤ cNL * g := by
    have e : (((L : ℝ) ^ 4 * c : ℝ) : ℂ) = (L : ℂ) ^ 4 * ((c : ℝ) : ℂ) := by push_cast; ring
    rw [e]; exact hnuS
  have b_n : ‖νh‖ ≤ Cf * g := hnu
  have b_k : ‖k0‖ ≤ κ0 := hk0
  have b_w : ‖w - 1‖ ≤ KT * mV := by
    have e : w = ((R.withMsq m).msq : ℂ) * (out.Z * tr) := by rw [hZz]; rfl
    rw [e]
    have h := hw
    rw [hVN] at h
    have e2 : KT * (R.withMsq m).msq * V = KT * mV := by
      show KT * m * V = KT * (m * V); ring
    linarith only [h, e2.le]
  have b_ah : ‖ah‖ ≤ ahi := by
    have := norm_le_insert' ah νh
    show ‖ah‖ ≤ Cf * g + h0ea L Cf D.ℓ g
    linarith only [this, b_n, b_a]
  have b_η : ‖ah - (((L : ℝ) ^ 4 * c : ℝ) : ℂ)‖ ≤ cNL * g + ea := by
    have e : ah - (((L : ℝ) ^ 4 * c : ℝ) : ℂ) = (ah - νh) + (νh - (((L : ℝ) ^ 4 * c : ℝ) : ℂ)) := by ring
    rw [e]; exact (norm_add_le _ _).trans (by linarith only [b_a, b_s])
  have b_aw : ‖ah * (w - 1)‖ ≤ ahi * (KT * mV) := by
    rw [norm_mul]; exact mul_le_mul b_ah b_w (norm_nonneg _) hahi0
  -- `Re n` and `|n|`
  have hnre : n.re = mV * (1 + k0.re) + ah.re + (ah * (w - 1)).re := by
    have e : n = ((m * V : ℝ) : ℂ) * (1 + k0) + ah + ah * (w - 1) := by rw [hn]; ring
    rw [e, hmV]; simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.one_re]
  have hk0re := abs_le.1 ((Complex.abs_re_le_norm k0).trans b_k)
  have haw := abs_le.1 ((Complex.abs_re_le_norm (ah * (w - 1))).trans b_aw)
  have har : |ah.re - (L : ℝ) ^ 4 * c| ≤ cNL * g + ea := by
    have := (Complex.abs_re_le_norm (ah - (((L : ℝ) ^ 4 * c : ℝ) : ℂ))).trans b_η
    rwa [Complex.sub_re, Complex.ofReal_re] at this
  have har' := abs_le.1 har
  have hnlo : mV * (1 - κ0) + (L : ℝ) ^ 4 * c - (cNL * g + ea) - ahi * (KT * mV) ≤ n.re := by
    rw [hnre]
    have q1 := mul_le_mul_of_nonneg_left hk0re.1 hmV0.le
    linarith only [q1, haw.1, har'.1]
  have hnhi : n.re ≤ mV * (1 + κ0) + (L : ℝ) ^ 4 * c + (cNL * g + ea) + ahi * (KT * mV) := by
    rw [hnre]
    have q2 := mul_le_mul_of_nonneg_left hk0re.2 hmV0.le
    linarith only [q2, haw.2, har'.2]
  have hnn : ‖n‖ ≤ h0nhi L Cf D.ℓ KT g mV := by
    show ‖n‖ ≤ mV * (1 + κ0) + ahi * (1 + KT * mV)
    have h1 : ‖((m * V : ℝ) : ℂ) * (1 + k0)‖ ≤ mV * (1 + κ0) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hmV0.le]
      exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by rw [norm_one]; linarith only [b_k]))
        hmV0.le
    have h2 : ‖ah * w‖ ≤ ahi * (1 + KT * mV) := by
      rw [norm_mul]
      refine mul_le_mul b_ah ?_ (norm_nonneg _) hahi0
      have := norm_le_insert' w 1
      rw [norm_one] at this; linarith only [this, b_w]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  -- `p` and the leading term
  set p : ℂ := 1 + k0 + ah * (w - 1) / ((m * V : ℝ) : ℂ) with hp
  have b_p : ‖p - 1‖ ≤ κ0 + ahi * KT := by
    have e : p - 1 = k0 + ah * (w - 1) / ((m * V : ℝ) : ℂ) := by rw [hp]; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add b_k ?_)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hmV0.le, div_le_iff₀ hmV0]
    calc ‖ah * (w - 1)‖ ≤ ahi * (KT * mV) := b_aw
      _ = ahi * KT * mV := by ring
  have hnU : ((m * V : ℝ) : ℂ) * (1 + (k0 + A * tr)) = n := wn2_n_eq hz A tr k0
  have hQ0 : 0 ≤ h0Q L Cf D.ℓ KT B D.ρ g mV := by
    unfold h0Q
    have : 0 ≤ h0nhi L Cf D.ℓ KT g mV := by linarith only [hnn, norm_nonneg n]
    have hρD : 0 ≤ D.ρ := hρ.le
    positivity
  -- the common estimate, given `n ≠ 0`
  have key : n ≠ 0 →
      1 + uFin (Nh + 1) out tr ≠ 0 ∧
      V / (z * ‖n‖ ^ 2) * (n.re - h0Q L Cf D.ℓ KT B D.ρ g mV) ≤
        (∑ x : Lam 2 L N, avg0 L N m b μ (psibar 0 * psi x)).re ∧
      (∑ x : Lam 2 L N, avg0 L N m b μ (psibar 0 * psi x)).re ≤
        V / (z * ‖n‖ ^ 2) * (n.re + h0Q L Cf D.ℓ KT B D.ρ g mV) := by
    intro hn0
    have hU : 1 + uFin (Nh + 1) out tr ≠ 0 := by
      intro h0; rw [hUeq] at h0; rw [← hnU, h0, mul_zero] at hn0; exact hn0 rfl
    refine ⟨hU, ?_⟩
    obtain ⟨-, hχ, -⟩ := D.onePtWinU R hP hi0 hRℓ hRA hRρ hN hNh hm hb hD hU
    have hG := suscept2_dressed_geo (R.withMsq m) hL7 hNh hρ8' hspl' hB hE' hm0 hm.2 hV hVL t hU
    have hZr : Zr (R.withMsq m) t (Nh + 2) = (z : ℂ) := hzZ
    rw [hZr] at hG
    have hG2 : ‖(∑ x : Lam 2 L N, avg0 L N m b μ (psibar 0 * psi x)) -
        (1 / ((m : ℂ) * (z : ℂ)) - (1 / (m : ℂ)) ^ 2 * (A / (z : ℂ)) / ((z : ℂ) * (1 + (k0 + A * tr))))‖ ≤
        ((L : ℝ) ^ 2) ^ (Nh + 1) / ‖(z : ℂ)‖ * Real.exp (64 / 7 * (R.withMsq m).ρ * B) *
          (24 * (R.withMsq m).ρ ^ 2 * B + 64 / 7 * (R.withMsq m).ρ * B *
            (‖A / (z : ℂ)‖ / (m * ‖1 + (k0 + A * tr)‖))) := by
      rw [hχ]; exact hG
    have hform := (wn2_chi0_form hm0 hV0 hz (A := A) (tr := tr) (k0 := k0) (by rwa [hUeq] at hU)).2
    rw [hform] at hG2
    -- the error in normalised form
    have hnorm_n : ‖n‖ = mV * ‖1 + (k0 + A * tr)‖ := by
      rw [← hnU, norm_mul, Complex.norm_real, Real.norm_of_nonneg hmV0.le]
    have hn0' : 0 < ‖n‖ := norm_pos_iff.2 hn0
    have hAz : ‖A / (z : ℂ)‖ = ‖ah‖ / V := by
      rw [hah, mul_div_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hV0.le]
      field_simp
    have hρD : 0 ≤ D.ρ := hρ.le
    set E2 := Real.exp (64 / 7 * D.ρ * B)
    have hE20 : 0 < E2 := Real.exp_pos _
    have herr : ((L : ℝ) ^ 2) ^ (Nh + 1) / ‖(z : ℂ)‖ * Real.exp (64 / 7 * (R.withMsq m).ρ * B) *
        (24 * (R.withMsq m).ρ ^ 2 * B + 64 / 7 * (R.withMsq m).ρ * B *
          (‖A / (z : ℂ)‖ / (m * ‖1 + (k0 + A * tr)‖))) ≤
        V / z * (24 * D.ρ ^ 2 * B * E2 / (L : ℝ) ^ 2 +
          64 / 7 * D.ρ * B * E2 / (L : ℝ) ^ 2 * ahi / ‖n‖) := by
      rw [hρR, Complex.norm_real, Real.norm_of_nonneg hz.le, hAz]
      exact h0_err_real hVL2 (by positivity) hz hm0 hV0 hρD hB hE20.le hnorm_n hn0' b_ah
    have hχb : ‖(∑ x : Lam 2 L N, avg0 L N m b μ (psibar 0 * psi x)) -
        (V : ℂ) * p / ((z : ℂ) * n)‖ ≤
        V / z * (24 * D.ρ ^ 2 * B * E2 / (L : ℝ) ^ 2 +
          64 / 7 * D.ρ * B * E2 / (L : ℝ) ^ 2 * ahi / ‖n‖) := by
      have e : (V : ℂ) * p / ((z : ℂ) * n) = (V : ℂ) * (1 + k0 + (V : ℂ) * A / (z : ℂ) *
          ((m : ℂ) * ((z : ℂ) * tr) - 1) / ((m * V : ℝ) : ℂ)) /
          ((z : ℂ) * (((m * V : ℝ) : ℂ) * (1 + k0) +
            (V : ℂ) * A / (z : ℂ) * ((m : ℂ) * ((z : ℂ) * tr)))) := rfl
      rw [e]; exact hG2.trans herr
    obtain ⟨r1, r2⟩ := wn2_re_bounds hV0 hz hn0 b_p hχb
    have hk : 0 ≤ V / (z * ‖n‖ ^ 2) := by positivity
    have hmono : (κ0 + ahi * KT) * ‖n‖ + 24 * D.ρ ^ 2 * B * E2 / (L : ℝ) ^ 2 * ‖n‖ ^ 2 +
        64 / 7 * D.ρ * B * E2 / (L : ℝ) ^ 2 * ahi * ‖n‖ ≤ h0Q L Cf D.ℓ KT B D.ρ g mV := by
      unfold h0Q
      have hn1 := norm_nonneg n
      have a1 : 0 ≤ κ0 + ahi * KT := by positivity
      have a2 : 0 ≤ 24 * D.ρ ^ 2 * B * E2 / (L : ℝ) ^ 2 := by positivity
      have a3 : 0 ≤ 64 / 7 * D.ρ * B * E2 / (L : ℝ) ^ 2 * ahi := by positivity
      have b1 := mul_le_mul_of_nonneg_left hnn a1
      have b2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn1 hnn 2) a2
      have b3 := mul_le_mul_of_nonneg_left hnn a3
      show (κ0 + ahi * KT) * ‖n‖ + 24 * D.ρ ^ 2 * B * E2 / (L : ℝ) ^ 2 * ‖n‖ ^ 2 +
          64 / 7 * D.ρ * B * E2 / (L : ℝ) ^ 2 * ahi * ‖n‖ ≤
        (κ0 + ahi * KT) * h0nhi L Cf D.ℓ KT g mV +
          24 * D.ρ ^ 2 * B * E2 / (L : ℝ) ^ 2 * h0nhi L Cf D.ℓ KT g mV ^ 2 +
          64 / 7 * D.ρ * B * E2 / (L : ℝ) ^ 2 * ahi * h0nhi L Cf D.ℓ KT g mV
      linarith only [b1, b2, b3]
    constructor
    · refine le_trans (mul_le_mul_of_nonneg_left ?_ hk) r1
      linarith only [hmono]
    · refine r2.trans (mul_le_mul_of_nonneg_left ?_ hk)
      linarith only [hmono]
  have hS : h0Slack L Cf D.ℓ cNL KT B D.ρ g mV =
      cNL * g + ea + ahi * (KT * mV) + mV * (1 + κ0) + h0Q L Cf D.ℓ KT B D.ρ g mV := rfl
  refine ⟨fun hup => ?_, fun hlo => ?_⟩
  · rw [hS] at hup
    have hpos : h0Q L Cf D.ℓ KT B D.ρ g mV < n.re := by linarith only [hnlo, hup, hmV0]
    have hn0 : n ≠ 0 := fun h => by rw [h, Complex.zero_re] at hpos; linarith only [hpos, hQ0]
    obtain ⟨hU, h1, -⟩ := key hn0
    refine ⟨hU, lt_of_lt_of_le ?_ h1⟩
    have hn0' : 0 < ‖n‖ := norm_pos_iff.2 hn0
    exact mul_pos (by positivity) (by linarith only [hpos])
  · rw [hS] at hlo
    have hneg : n.re + h0Q L Cf D.ℓ KT B D.ρ g mV < 0 := by linarith only [hnhi, hlo]
    have hn0 : n ≠ 0 := fun h => by
      rw [h, Complex.zero_re] at hneg; linarith only [hneg, hQ0]
    obtain ⟨hU, -, h2⟩ := key hn0
    refine ⟨hU, lt_of_le_of_lt h2 ?_⟩
    have hn0' : 0 < ‖n‖ := norm_pos_iff.2 hn0
    exact mul_neg_of_pos_of_neg (by positivity) hneg

/-! ### The window inputs -/

/-- **The last-two-step mass flow along windowed trajectories** (any sign of `h`). -/
theorem MasterCore.h0Mass {L : ℕ} [NeZero L] (D : MasterCore L) :
    ∃ KT B : ℝ, 0 ≤ KT ∧ 0 ≤ B ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = D.ℓ → R.A = D.A → R.ρ = D.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
    ∀ b μ : ℝ, 0 < b →
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ j)) →
      H0MassEnd R m b μ Nh (h0Slack L D.Cf D.ℓ (cNuLast (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.ε) KT B
        D.ρ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).1 (m * Fintype.card (Lam 2 L N))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hspl, -⟩ := D.hC2
  obtain ⟨-, B, hB, hE⟩ := id hspl
  obtain ⟨KT, hKT, hZT⟩ := lastOut_zeroT D.hZT
  exact ⟨KT, B, hKT, hB, D.h0MassAt hKT hB hE hZT⟩

/-- **The mass flow at the canonical constants** `h0KT`, `h0B` (those of the `ε`-requirement
`h0EReq`). -/
theorem MasterCore.h0MassC {L : ℕ} [NeZero L] (D : MasterCore L) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = D.ℓ → R.A = D.A → R.ρ = D.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
    ∀ b μ : ℝ, 0 < b →
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ j)) →
      H0MassEnd R m b μ Nh (h0Slack L D.Cf D.ℓ (cNuLast (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.ε)
        (h0KT L D.ρ) (h0B L D.ρ) D.ρ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).1
        (m * Fintype.card (Lam 2 L N))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hspl, -⟩ := D.hC2
  exact D.h0MassAt (h0KT_spec D.hZT).1 (h0B_spec hspl).1 (h0B_spec hspl).2 (h0KT_spec D.hZT).2

/-- **The upper window end from `Re χ > 0`**: with `⟨Z_0⟩ ≠ 0` and `r = 1 − b⟨ψ̄_0ψ_0⟩` real
`≥ 0`, the Ward identity gives `h'Re χ = r`, so `h' = μ + m² − b ≥ 0`; then positivity makes `χ`
real, hence `χ > 0`. -/
theorem h0OnePtUp_of_re {L N : ℕ} [NeZero L] {m b μ : ℝ} (hb : 0 < b) (hm0 : 0 < m)
    (hZ : Obs.Zb (Suscept.Cov 2 L N m) (VE (V0c b μ) (univ : Finset (Lam 2 L N))) ≠ 0)
    (hr : ∃ r : ℝ, 0 ≤ r ∧ 1 - (b : ℂ) * avg0 L N m b μ (psibar 0 * psi 0) = r)
    (hχ : 0 < (∑ x : Lam 2 L N, avg0 L N m b μ (psibar 0 * psi x)).re) :
    H0OnePtUp L N m b μ := by
  obtain ⟨r, hr0, hre⟩ := hr
  have hw := ward_V0 (L := L) (N := N) hb hm0 hZ
  rw [hre] at hw
  have h1 := congrArg Complex.re hw
  rw [Complex.ofReal_re, Complex.re_ofReal_mul] at h1
  have hh : b ≤ μ + m := by
    by_contra hc
    push Not at hc
    have : (μ + m - b) * (∑ x : Lam 2 L N, avg0 L N m b μ (psibar 0 * psi x)).re < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hχ
    linarith
  obtain ⟨χ, -, -, hχe⟩ := chi_mem_of_h_nonneg (L := L) (N := N) hb hm0 hh
  refine ⟨hZ, ⟨r, hr0, hre⟩, ⟨χ, ?_, hχe⟩⟩
  rw [hχe, Complex.ofReal_re] at hχ
  exact hχ

/-- **The lower window end from `Re χ < 0`** at one point of the window. -/
theorem h0SusceptExit_of_re {L N : ℕ} [NeZero L] {m b μl μu : ℝ} {μ : ℝ} (hμ : μ ∈ Icc μl μu)
    (hχ : (∑ x : Lam 2 L N, avg0 L N m b μ (psibar 0 * psi x)).re < 0) :
    H0SusceptExit L N m b μl μu := by
  refine ⟨μ, hμ, fun ⟨χ, h0, _, he⟩ => ?_⟩
  rw [he, Complex.ofReal_re] at hχ
  linarith

end

end Spin2
