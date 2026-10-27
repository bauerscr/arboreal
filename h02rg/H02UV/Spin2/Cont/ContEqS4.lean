import Spin2.Cont.ContFin1
import Spin2.Cont.ContFin2
import Spin2.Cont.ContTheta

set_option autoImplicit false

/-!
# B3, `r`-dependent form: scalar helpers for the discharge of `fin_T6_mid` / `fin_conn_diff_top`

* `eqs_mul_le_of_mem`: smallness from one threshold `g·(∑|aᵢ| + 1) ≤ 1` for every coefficient `aᵢ`
  of a list.
* The `C_δ`-constants (`Θ(C_δ) = e^{2c_δ'}(81/56)^{C_δ}` bounds `Θ_b(j)` for `N_h − j ≤ C_δ`):
  `eqsTh`, `eqsKb` (`≥ k̄`), `eqsTw`, `eqsTk` (bounds of `w/(s²M₀)`, `k/(s²M₀)`), `eqsW2`, `eqsWT`,
  `eqsVT`, `eqsM0` (the `m₀` of `h8*`).
* `eqs_ratio_w`, `eqs_ratio_k`: from `1344(8c_Nk + Γ_ww) ≤ S`: `w/S ≤ eqsTw`, `(k + 120B(cε)w)/S ≤ eqsTk`.
* `eqs_bt2_le3`: `|β^{(y−x,y)}_{ms}| ≤ 3|β^{(0,y)}_{ms}|` (from `cdd_art_rel`).
* **`eqs_zab_le`**: `Z_{ab}/(c_{ab}r_{ms}) ≤ (7/5)^{J−ms}Θ_b(ms)·eqsK2/ǧ_{ms}²` with
  `eqsK2 = 16c_W² + 12ι_ZA/(c_{ab}c)`.
* Monotonicity: `eqs_naKA_mono`, `eqs_rpKE_mono`, `eqs_ctVT_mono`, `eqs_rptfWT_mono`,
  `eqs_rptfKx_mono`, `eqs_rpIota_mono`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

/-- Smallness of every coefficient of a list from one threshold. -/
theorem eqs_mul_le_of_mem {l : List ℝ} {a g : ℝ} (ha : a ∈ l) (hg : 0 ≤ g)
    (hT : g * ((l.map abs).sum + 1) ≤ 1) : a * g ≤ 1 := by
  have h1 : |a| ≤ (l.map abs).sum := by
    have := List.single_le_sum (l := l.map abs) (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg y) |a|
      (List.mem_map_of_mem ha)
    exact this
  have h2 : a * g ≤ |a| * g := mul_le_mul_of_nonneg_right (le_abs_self a) hg
  have h3 : |a| * g ≤ (l.map abs).sum * g := mul_le_mul_of_nonneg_right h1 hg
  nlinarith

/-- The threshold `1/(∑|aᵢ| + 1)`. -/
def eqsThr (l : List ℝ) : ℝ := 1 / ((l.map abs).sum + 1)

theorem eqsThr_pos (l : List ℝ) : 0 < eqsThr l := by
  unfold eqsThr
  have : 0 ≤ (l.map abs).sum := List.sum_nonneg (fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg y)
  positivity

theorem eqs_le_thr {l : List ℝ} {a g : ℝ} (ha : a ∈ l) (hg : 0 ≤ g) (hgT : g ≤ eqsThr l) :
    a * g ≤ 1 := by
  refine eqs_mul_le_of_mem ha hg ?_
  have : 0 ≤ (l.map abs).sum := List.sum_nonneg (fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg y)
  unfold eqsThr at hgT
  rwa [le_div_iff₀ (by linarith)] at hgT

/-- `a·g ≤ c` from `(a/c)·g ≤ 1`, `c > 0`. -/
theorem eqs_le_of_div {a c g : ℝ} (hc : 0 < c) (h : a / c * g ≤ 1) : a * g ≤ c := by
  have e : a * g = c * (a / c * g) := by field_simp
  rw [e]; nlinarith

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

/-- `Θ(C_δ) = e^{2c_δ'}(81/56)^{C_δ}`. -/
def eqsTh (Cδ : ℕ) : ℝ :=
  Real.exp (2 * (M.core.cRel * (4 / betaL L) * M.core.ε)) * (81 / 56) ^ Cδ

/-- `k̄(C_δ) = (c_W + 1)(1 + Θ(C_δ)) + 1`. -/
def eqsKb (Cδ : ℕ) : ℝ := (M.core.cWo + 1) * (1 + M.eqsTh Cδ) + 1

/-- The bound `1/(1344Γ_w)` of `w/(s²M₀)`. -/
def eqsTw : ℝ := 1 / (1344 * M.core.rdtΓ)

/-- The bound of `(k + 120B(cε)w)/(s²M₀)`. -/
def eqsTk : ℝ :=
  1 / (1344 * (8 * (PtCorr2.csN 2 : ℝ))) + 120 * M.core.Bk * (M.core.c * M.core.ε) * M.eqsTw

/-- `w₂(C_δ) = exp(L²C_w(c + (2k̄)²)) − 1`. -/
def eqsW2 (Cδ : ℕ) : ℝ :=
  Real.exp ((L : ℝ) ^ 2 * (M.core.Cw * (M.core.c + (2 * M.eqsKb Cδ) ^ 2))) - 1

/-- `w_T(C_δ)`. -/
def eqsWT (Cδ : ℕ) : ℝ :=
  M.core.cWo * M.core.c + M.eqsTw + M.eqsTh Cδ * (M.core.cWo * M.core.c) + M.eqsW2 Cδ

/-- `v_T(C_δ) = 1 + Θ(C_δ)`. -/
def eqsVT (Cδ : ℕ) : ℝ := 1 + M.eqsTh Cδ

/-- `m₀(C_δ)` of `h8*`. -/
def eqsM0 (C₁w C₁t C₁v C₁m : ℝ) (Cδ : ℕ) : ℝ :=
  8 * (2 * rpIota (M.eqsVT Cδ) (M.eqsWT Cδ) * M.core.A) ^ ((L + 18) ^ 2) *
    (1 / (vck C₁w * (4 * C₁w + 1)) + 1 / (vck C₁t * (4 * C₁t + 1)) +
      1 / (vck C₁v * (4 * C₁v + 1)) + 1 / (vck C₁m * (4 * C₁m + 1)))

/-- `16c_W² + 12ι_ZA/(c_{ab}c)`. -/
def eqsK2 : ℝ := 16 * M.core.cWo ^ 2 + 12 * (zabIota M.core.cWo * M.core.A) / (M.k2cab * M.core.c)

theorem eqsTh_pos (Cδ : ℕ) : 0 < M.eqsTh Cδ := by unfold eqsTh; positivity

theorem cw2Thb_le_eqsTh {Nh j Cδ : ℕ} (h : Nh - j ≤ Cδ) : cw2Thb M Nh j ≤ M.eqsTh Cδ := by
  unfold cw2Thb eqsTh
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) h) (Real.exp_pos _).le

theorem cw2Thb_nonneg (Nh j : ℕ) : 0 ≤ cw2Thb M Nh j := by unfold cw2Thb; positivity

theorem k2mbar_le_eqsKb {Nh j Cδ : ℕ} (h : Nh - j ≤ Cδ) : k2mbar M Nh j ≤ M.eqsKb Cδ := by
  unfold k2mbar eqsKb
  have := M.cw2Thb_le_eqsTh h
  have := M.core.consts_nonneg.2.2.2.2.2.1
  nlinarith

theorem k2mbar_nonneg (Nh j : ℕ) : 0 ≤ k2mbar M Nh j := by
  unfold k2mbar
  have := M.cw2Thb_nonneg Nh j
  have := M.core.consts_nonneg.2.2.2.2.2.1
  positivity

/-- `w/S ≤ eqsTw` (`Γ_w > 0`). -/
theorem eqs_ratio_w {kk ww S : ℝ} (hΓ : 0 < M.core.rdtΓ) (hkk : 0 ≤ kk)
    (hS : 0 ≤ S) (h : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤ S) :
    ww / S ≤ M.eqsTw := by
  have hT : 0 ≤ M.eqsTw := by unfold eqsTw; positivity
  rcases eq_or_lt_of_le hS with h0 | hS
  · rw [← h0, div_zero]; exact hT
  unfold eqsTw
  rw [div_le_div_iff₀ hS (by positivity)]
  have : 0 ≤ 8 * (PtCorr2.csN 2 : ℝ) * kk := by positivity
  nlinarith

/-- `(k + 120B(cε)w)/S ≤ eqsTk` (`c_N ≥ 1`, `Γ_w > 0`). -/
theorem eqs_ratio_k {kk ww S : ℝ} (hΓ : 0 < M.core.rdtΓ) (hcN : (1 : ℝ) ≤ PtCorr2.csN 2)
    (hBc : 0 ≤ 120 * M.core.Bk * (M.core.c * M.core.ε)) (hkk : 0 ≤ kk) (hww : 0 ≤ ww)
    (hS : 0 ≤ S) (h : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤ S) :
    (kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / S ≤ M.eqsTk := by
  have hw := M.eqs_ratio_w hΓ hkk hS h
  have hT : 0 ≤ M.eqsTk := by
    unfold eqsTk eqsTw; positivity
  rcases eq_or_lt_of_le hS with h0 | hS
  · rw [← h0, div_zero]; exact hT
  have hk : kk / S ≤ 1 / (1344 * (8 * (PtCorr2.csN 2 : ℝ))) := by
    rw [div_le_div_iff₀ hS (by positivity)]
    have : 0 ≤ M.core.rdtΓ * ww := by positivity
    nlinarith
  unfold eqsTk
  rw [add_div, mul_div_assoc]
  have := mul_le_mul_of_nonneg_left hw hBc
  linarith

end MasterFacts

/-! ### Monotonicity of the constants -/

namespace MasterFacts

variable (M : MasterFacts L)

theorem eqs_rpIota_mono {v w v' w' : ℝ} (hw : 0 ≤ w) (hv : v ≤ v') (hw' : w ≤ w') :
    rpIota v w ≤ rpIota v' w' := by
  unfold rpIota
  exact mul_le_mul (Real.exp_le_exp.2 (by linarith)) (by linarith) (by linarith)
    (Real.exp_pos _).le

theorem eqs_naKA_mono {cV cW cK cV' cW' cK' r₀ : ℝ} (hr₀ : 0 < r₀)
    (h : cV + cW + 8 * cK ≤ cV' + cW' + 8 * cK') : M.naKA cV cW cK r₀ ≤ M.naKA cV' cW' cK' r₀ := by
  unfold naKA
  have hu := pairUnitC_nonneg M
  have hJ := cJab_nonneg L hr₀
  have hF := M.topF'_nonneg
  have hC := M.topCL_nonneg
  have hQ : 0 ≤ Q1 2 := by have := one_le_Q1 (d := 2) (by norm_num); linarith
  have hLab : 0 ≤ cLab L := by unfold cLab; positivity
  have t1 : cLab L * (cV + cW + 8 * cK + 1) * pairUnitC M ≤
      cLab L * (cV' + cW' + 8 * cK' + 1) * pairUnitC M :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hLab) hu
  have t2 : 81 / 32 * cJab L r₀ * (cV + cW + 8 * cK + 1) ≤
      81 / 32 * cJab L r₀ * (cV' + cW' + 8 * cK' + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have t3 : 0 ≤ 2 * (1 + M.topF' + M.topCL) := by positivity
  have t4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (show 1 / 2 + 81 / 32 * cJab L r₀ * (cV + cW + 8 * cK + 1) ≤
      1 / 2 + 81 / 32 * cJab L r₀ * (cV' + cW' + 8 * cK' + 1) by linarith)
    (by norm_num : (0 : ℝ) ≤ 8)) t3
  linarith

theorem eqs_rpKE_mono {cK cK' r₀ : ℝ} (hr₀ : 0 < r₀) (h : cK ≤ cK') :
    M.rpKE cK r₀ ≤ M.rpKE cK' r₀ := by
  unfold rpKE
  have hu := pairUnitC_nonneg M
  have hJ := cJab_nonneg L hr₀
  have hF := M.topF'_nonneg
  have hC := M.topCL_nonneg
  have hQ : 0 ≤ Q1 2 := by have := one_le_Q1 (d := 2) (by norm_num); linarith
  have hLab : 0 ≤ cLab L := by unfold cLab; positivity
  have t1 : cLab L * (8 * cK + 1) * pairUnitC M ^ 2 ≤ cLab L * (8 * cK' + 1) * pairUnitC M ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hLab) (by positivity)
  have t2 : 81 / 32 * cJab L r₀ * (8 * cK + 1) ≤ 81 / 32 * cJab L r₀ * (8 * cK' + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have t3 : 0 ≤ pairUnitC M * (2 * (1 + M.topF' + M.topCL)) := by positivity
  have t4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (show 1 / 2 + 81 / 32 * cJab L r₀ * (8 * cK + 1) ≤ 1 / 2 + 81 / 32 * cJab L r₀ * (8 * cK' + 1)
      by linarith) (by norm_num : (0 : ℝ) ≤ 8)) t3
  have e1 : 8 * (1 / 2 + 81 / 32 * cJab L r₀ * (8 * cK + 1)) * pairUnitC M *
      (2 * (1 + M.topF' + M.topCL)) = 8 * (1 / 2 + 81 / 32 * cJab L r₀ * (8 * cK + 1)) *
      (pairUnitC M * (2 * (1 + M.topF' + M.topCL))) := by ring
  have e2 : 8 * (1 / 2 + 81 / 32 * cJab L r₀ * (8 * cK' + 1)) * pairUnitC M *
      (2 * (1 + M.topF' + M.topCL)) = 8 * (1 / 2 + 81 / 32 * cJab L r₀ * (8 * cK' + 1)) *
      (pairUnitC M * (2 * (1 + M.topF' + M.topCL))) := by ring
  linarith

theorem eqs_ctVT_mono {r r' : ℝ} (hr : 0 ≤ r) (h : r ≤ r') : M.ctVT r ≤ M.ctVT r' := by
  unfold ctVT
  have hδ := M.core.consts_nonneg.2.2.2.2.2.2.2.1
  have : r ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ hr h 2
  have := mul_le_mul_of_nonneg_left this hδ
  nlinarith

theorem eqs_rptfWT_mono {r mm r' mm' : ℝ} (hCw : 0 ≤ M.core.Cw) (hmm : 0 ≤ mm) (hr : r ≤ r')
    (h : mm ≤ mm') : M.rptfWT r mm ≤ M.rptfWT r' mm' := by
  unfold rptfWT
  have : mm ^ 2 ≤ mm' ^ 2 := pow_le_pow_left₀ hmm h 2
  have h2 : M.core.Cw * (r + mm ^ 2) ≤ M.core.Cw * (r' + mm' ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hCw
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
  have := Real.exp_le_exp.2 h3
  linarith

theorem eqs_rptfKx_mono {c₁ r mm k₁ c₁' r' mm' k₁' : ℝ} (hc₁ : 0 ≤ c₁) (hr : 0 ≤ r)
    (hmm : 0 ≤ mm) (hk₁ : 0 ≤ k₁) (h1 : c₁ ≤ c₁') (h2 : r ≤ r') (h3 : mm ≤ mm') (h4 : k₁ ≤ k₁') :
    M.rptfKx c₁ r mm k₁ ≤ M.rptfKx c₁' r' mm' k₁' := by
  unfold rptfKx
  have hA2 := M.core.hA2
  have hL : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hC₀ : 0 ≤ M.core.C₀o := M.core.hC₀o
  have hθ : 0 ≤ kθ0 L M.core.A M.core.C₀o M.core.ηo := by
    unfold kθ0
    exact mul_nonneg hC₀ (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hcx : 0 < cx M.core.κ M.core.cT := by
    obtain ⟨-, -, -, -, hκ0, hκ1, -, -, hcT, -⟩ := id M.core.hC2
    unfold cx; exact div_pos (by linarith) (by linarith)
  have hC₁ : 0 ≤ M.core.C₁k := M.core.hC₁k
  have hB : 0 ≤ kB (kθ0 L M.core.A M.core.C₀o M.core.ηo) M.core.C₁k (8 * cx M.core.κ M.core.cT) := by
    unfold kB; positivity
  have hc₁' : 0 ≤ c₁' := hc₁.trans h1
  have hr' : 0 ≤ r' := hr.trans h2
  have a1 : M.core.C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 8 * c₁) * r ≤
      M.core.C₁k * (2 + 2 * (8 * cx M.core.κ M.core.cT) + 8 * c₁') * r' := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC₁) h2 hr (by positivity)
  have a2 := mul_le_mul (add_le_add_left a1 (kθ0 L M.core.A M.core.C₀o M.core.ηo))
    (show 8 * k₁ ≤ 8 * k₁' by linarith) (by positivity) (by positivity)
  have a3 : r ^ 2 * mm ≤ r' ^ 2 * mm' :=
    mul_le_mul (pow_le_pow_left₀ hr h2 2) h3 hmm (by positivity)
  have a4 := mul_le_mul_of_nonneg_left a3 hB
  have e1 : kB (kθ0 L M.core.A M.core.C₀o M.core.ηo) M.core.C₁k (8 * cx M.core.κ M.core.cT) *
      r ^ 2 * mm = kB (kθ0 L M.core.A M.core.C₀o M.core.ηo) M.core.C₁k (8 * cx M.core.κ M.core.cT) *
      (r ^ 2 * mm) := by ring
  have e2 : kB (kθ0 L M.core.A M.core.C₀o M.core.ηo) M.core.C₁k (8 * cx M.core.κ M.core.cT) *
      r' ^ 2 * mm' = kB (kθ0 L M.core.A M.core.C₀o M.core.ηo) M.core.C₁k (8 * cx M.core.κ M.core.cT) *
      (r' ^ 2 * mm') := by ring
  linarith

end MasterFacts


/-! ### The `Z_{ab}` waiting term -/

namespace MasterFacts

variable (M : MasterFacts L)

set_option maxHeartbeats 2000000 in
/-- `|β^{(y−x,y)}_{ms}| ≤ 3|β^{(0,y)}_{ms}|` (`cdd_art_rel`). -/
theorem eqs_bt2_le3 (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc)
    (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ)
    (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x y : Lam 2 L N) {ms : ℕ} (hk0 : 0 < ms) (hkN : ms < Nh)
    (hs0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 + zA L m ms))
    (hs : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ ms).1 + zA L m ms) ≤ 1 / 2) :
    ‖bt2 R (pl2Pts x y) (zV0 b) m b μ₀ ms‖ ≤ 3 * ‖bt2 R (ptsX y) (zV0 b) m b μ₀ ms‖ := by
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have h := cdd_art_rel R (pl2Pts x y) (ptsX y) (zV b) (zV_mua_ne hb0)
    (M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN hNh hm hD (pl2Pts x y))
    (M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN hNh hm hD (ptsX y)) hkN hs0 hs
  rw [cdd_bt2_zV0 R (pl2Pts x y) m b μ₀ hk0, cdd_bt2_zV0 R (ptsX y) m b μ₀ hk0] at h
  have t1 := norm_le_norm_add_norm_sub' (bt2 R (pl2Pts x y) (zV0 b) m b μ₀ ms)
    (bt2 R (ptsX y) (zV0 b) m b μ₀ ms)
  have t2 := mul_le_mul_of_nonneg_right hs (norm_nonneg (bt2 R (ptsX y) (zV0 b) m b μ₀ ms))
  nlinarith [norm_nonneg (bt2 R (ptsX y) (zV0 b) m b μ₀ ms)]

/-- `ǧ|β'| ≤ M₀` (pure). -/
theorem eqs_cddM_ge {Kl g z bb bb' s ι A : ℝ} (r : ℕ) (hKl : 0 ≤ Kl * (g + z)) (hg : 0 ≤ g)
    (hbb : 0 ≤ bb) (hbb' : 0 ≤ bb') (hs : 0 < s) (hι : 0 ≤ ι) (hA : 0 ≤ A) (hc : 0 ≤ M.core.c)
    (hΓ : 0 ≤ M.core.rdtΓ) : g * bb' ≤ M.cddM Kl g z bb bb' s ι A r := by
  unfold MasterFacts.cddM
  refine le_add_of_nonneg_left ?_
  have hcst := M.core.consts_nonneg
  have hcW : 1 ≤ M.core.cWo := hcst.2.2.2.2.2.1
  have hBk : 0 ≤ M.core.Bk := hcst.2.2.2.2.2.2.1
  have hcδ : 0 ≤ M.core.cδ := hcst.2.2.2.2.2.2.2.1
  have hβL := ct_betaL_pos M.ct_L2
  positivity

end MasterFacts

/-- The `Z_{ab}` ratio, pure form: with `|β| ≤ 3|β'|`, `ǧ|β'| ≤ M₀`, `σ ≤ 4ι_ZA`:
`q Θ/M₀·(|β|(α + σ) + |β'|α)/(c_{ab}cǧ) ≤ qΘ(16c_W² + 12ι_ZA/(c_{ab}c))/ǧ²`,
`α = c_{ab}cǧ(2c_W)²`. -/
theorem eqs_zab_pure {q Θ g bb bb' M₀ σ ιA cab c cW : ℝ} (hq : 0 ≤ q) (hΘ : 0 ≤ Θ) (hg : 0 < g)
    (hg1 : g ≤ 1) (hbb' : 0 ≤ bb') (h3 : bb ≤ 3 * bb') (hM0 : g * bb' ≤ M₀) (hσ0 : 0 ≤ σ)
    (hσ : σ ≤ 4 * ιA) (hcab : 0 < cab) (hc : 0 < c) :
    q * Θ / M₀ * (bb * (cab * (c * g) * (2 * cW) ^ 2 + σ) + bb' * (cab * (c * g) * (2 * cW) ^ 2)) /
        (cab * (c * g)) ≤
      q * Θ * (16 * cW ^ 2 + 12 * ιA / (cab * c)) / g ^ 2 := by
  set α := cab * (c * g) * (2 * cW) ^ 2 with hαd
  have hα : 0 ≤ α := by positivity
  have hιA : 0 ≤ ιA := by linarith
  have hX : bb * (α + σ) + bb' * α ≤ bb' * (4 * α + 12 * ιA) := by
    have := mul_le_mul h3 (show α + σ ≤ α + 4 * ιA by linarith) (by linarith) (by positivity)
    nlinarith
  have hqΘ : 0 ≤ q * Θ := mul_nonneg hq hΘ
  have hZ : q * Θ / M₀ * (bb * (α + σ) + bb' * α) ≤ q * Θ * (4 * α + 12 * ιA) / g := by
    rcases eq_or_lt_of_le hbb' with h0 | hpos
    · have hX0 : bb * (α + σ) + bb' * α ≤ 0 := by
        have : bb' * (4 * α + 12 * ιA) = 0 := by rw [← h0]; ring
        linarith
      have hM : 0 ≤ M₀ := by
        have : g * bb' = 0 := by rw [← h0]; ring
        linarith
      have : q * Θ / M₀ * (bb * (α + σ) + bb' * α) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (div_nonneg hqΘ hM) hX0
      have : 0 ≤ q * Θ * (4 * α + 12 * ιA) / g := by positivity
      linarith
    · have hM0p : 0 < M₀ := lt_of_lt_of_le (mul_pos hg hpos) hM0
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hM0p hg]
      have h1 := mul_le_mul_of_nonneg_left hX hqΘ
      have h2 := mul_le_mul_of_nonneg_left hM0 (show 0 ≤ q * Θ * (4 * α + 12 * ιA) by positivity)
      nlinarith [mul_le_mul_of_nonneg_right h1 hg.le]
  have hcg : 0 < cab * (c * g) := by positivity
  rw [div_le_div_iff₀ hcg (by positivity)]
  have hZ' := mul_le_mul_of_nonneg_right hZ (sq_nonneg g)
  refine hZ'.trans ?_
  have key : (4 * α + 12 * ιA) * g ≤ (16 * cW ^ 2 + 12 * ιA / (cab * c)) * (cab * (c * g)) := by
    have e : (16 * cW ^ 2 + 12 * ιA / (cab * c)) * (cab * (c * g)) =
        16 * cW ^ 2 * (cab * c) * g + 12 * ιA * g := by
      field_simp
    rw [e, hαd]
    have : 12 * ιA * g ≤ 12 * ιA := by nlinarith
    nlinarith
  have e1 : q * Θ * (4 * α + 12 * ιA) / g * g ^ 2 = q * Θ * ((4 * α + 12 * ιA) * g) := by
    field_simp
  rw [e1]
  have := mul_le_mul_of_nonneg_left key hqΘ
  linarith

namespace MasterFacts

variable (M : MasterFacts L)

set_option maxHeartbeats 4000000 in
/-- **The `Z_{ab}` ratio**: `Z_{ab}/(c_{ab}r_{ms}) ≤ (7/5)^{J−ms}Θ_b(ms)·eqsK2/ǧ_{ms}²`. -/
theorem eqs_zab_le (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc)
    (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ)
    (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (x y : Lam 2 L N) {ms J : ℕ} (r : ℕ) (hk0 : 0 < ms) (hkN : ms < Nh)
    (hs0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms))
    (hs : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) ≤ 1 / 2)
    (hsup : (supNorm (y - x) : ℝ) ≤ (L : ℝ) ^ ms) (hcab : 0 < M.k2cab) (hc1 : 1 ≤ M.core.c)
    (hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ≤ 1) :
    zabZr M R m b (b - m) x y ms (M.pl5M0 R m b x y ms r) J Nh /
        (M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1)) ≤
      (7 / 5) ^ (J - ms) * cw2Thb M Nh ms * M.eqsK2 /
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 2 := by
  have h3 := M.eqs_bt2_le3 N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD x y hk0 hkN hs0 hs
  have hgp : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 := (hD ms (by omega)).1
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, -⟩ := id M.core.hC2
  have hρ0' : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8
  have hsp := histS_pos' (R.withMsq m) hρ0' hρ8' (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ms
  have hA0 : 0 ≤ (R.withMsq m).A := by
    rw [show (R.withMsq m).A = M.core.A from hRA]; linarith [M.core.hA2]
  have hε0 : 0 ≤ M.core.ε := by
    have := (hD 0 (Nat.zero_le _)).2.1; linarith [(hD 0 (Nat.zero_le _)).1]
  have hΓ := M.core.rdtΓ_nonneg (by linarith) hε0
  have hι : 0 ≤ rpIota 0 0 := by
    have := one_le_rpIota (le_refl (0 : ℝ)) (le_refl (0 : ℝ)); linarith
  have hM0 := M.eqs_cddM_ge (Kl := M.Kp) (z := zA L m ms)
    (bb := ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖) r hs0 hgp.le (norm_nonneg _)
    (norm_nonneg (bt2 R (ptsX y) (zV0 b) m b (b - m) ms)) hsp hι hA0 (by linarith) hΓ
  have hLm : (0 : ℝ) < (L : ℝ) ^ ms := by
    have : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L)); positivity
  have hcW : 1 ≤ M.core.cWo := M.core.consts_nonneg.2.2.2.2.2.1
  have hιZ : 0 ≤ zabIota M.core.cWo * M.core.A := by
    unfold zabIota; have := M.core.hA2; positivity
  have hσ : 4 * (supNorm (y - x) : ℝ) / (L : ℝ) ^ ms * zabIota M.core.cWo * M.core.A ≤
      4 * (zabIota M.core.cWo * M.core.A) := by
    have : (supNorm (y - x) : ℝ) / (L : ℝ) ^ ms ≤ 1 := by rw [div_le_one hLm]; exact hsup
    have h0 : 0 ≤ (supNorm (y - x) : ℝ) / (L : ℝ) ^ ms := by positivity
    have e : 4 * (supNorm (y - x) : ℝ) / (L : ℝ) ^ ms * zabIota M.core.cWo * M.core.A =
        4 * ((supNorm (y - x) : ℝ) / (L : ℝ) ^ ms) * (zabIota M.core.cWo * M.core.A) := by ring
    rw [e]; nlinarith
  have hσ0 : 0 ≤ 4 * (supNorm (y - x) : ℝ) / (L : ℝ) ^ ms * zabIota M.core.cWo * M.core.A := by
    have := M.core.hA2; unfold zabIota; positivity
  unfold zabZr
  exact eqs_zab_pure (by positivity) (M.cw2Thb_nonneg Nh ms) hgp hg1 (norm_nonneg _) h3 hM0 hσ0 hσ
    hcab (by linarith)

end MasterFacts


end

end Spin2
