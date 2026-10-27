import Ward.MainLimits
import FRD.GreenAsymp
import FRD.GreenBd

/-!
# The estimates of `thm:h02` at `h = 0`

At `h = 0` the solution of `cor:ward` (ii) is `(b*, 0)` with `β(b*, 0) = β`; with
`s = s₀(b*, 0)`, `|s| ≤ min(1/2, 2C b*)`, one has `c² = (1+s)/β` and `b* = (1+s)²/β`.
With `E(a) = |x|^{-a}` (Euclidean norm):

* `est_θ`: `|θ - 1| ≤ K/β`, `θ = θh(β, 0) = Re(1 - c² Γ(0, b*))`;
* `est_τ`: `|τ₀(x) - (1+s) c_d E(d-2)/β| ≤ K E(d-2+κ')/β`, `τ₀ = τh(β, x, 0)`;
* `est_σ`: `|σ₀(x) + Re((1+s)²Λ²) c_d² E(2(d-2))/β²| ≤ K E(2(d-2)+κ')/β²`, `σ₀ = σh(β, x, 0)`,
  `Λ = Λ(0, b*)`;
* `est_c1`, `est_c2`: `|(1+s) c_d - c_d| ≤ K/β`, `|Re((1+s)²Λ²) c_d² - c_d²| ≤ K/β`.

The inputs (bounds at `m² = 0` from `Ward.ObsLimit*`, the asymptotics of `G = greenZd`) are
hypotheses of the section.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Metric Filter Topology FRD.GreenAsymp

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-! ### Norm conversions -/

theorem one_le_eNorm {x : Zd d} (hx : x ≠ 0) : 1 ≤ eNorm x :=
  le_trans (by exact_mod_cast one_le_supNormZ hx) (supNormZ_le_eNorm x)

theorem supNorm_rpow_le {x : Zd d} (hx : x ≠ 0) {a : ℝ} (ha : 0 ≤ a) :
    (supNormZ x : ℝ) ^ (-a) ≤ Real.sqrt d ^ a * eNorm x ^ (-a) := by
  have hr : (1 : ℝ) ≤ supNormZ x := by exact_mod_cast one_le_supNormZ hx
  have hd : 0 < Real.sqrt d := by
    have : (1 : ℝ) ≤ supNormZ x := hr
    have h2 := eNorm_le_supNormZ x
    have h3 := one_le_eNorm hx
    by_contra h
    push_neg at h
    have : Real.sqrt d = 0 := le_antisymm h (Real.sqrt_nonneg _)
    rw [this, zero_mul] at h2; linarith
  have hle : eNorm x / Real.sqrt d ≤ supNormZ x := by
    rw [div_le_iff₀ hd, mul_comm]; exact eNorm_le_supNormZ x
  have he : 0 < eNorm x / Real.sqrt d := div_pos (by linarith [one_le_eNorm hx]) hd
  calc (supNormZ x : ℝ) ^ (-a) ≤ (eNorm x / Real.sqrt d) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos he hle (by linarith)
    _ = Real.sqrt d ^ a * eNorm x ^ (-a) := by
        rw [Real.div_rpow (by linarith [one_le_eNorm hx]) hd.le, Real.rpow_neg hd.le,
          div_inv_eq_mul, mul_comm]

theorem eNorm_rpow_anti {x : Zd d} (hx : x ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    eNorm x ^ (-b) ≤ eNorm x ^ (-a) :=
  Real.rpow_le_rpow_of_exponent_le (one_le_eNorm hx) (by linarith)

theorem eNorm_rpow_nonneg (x : Zd d) (a : ℝ) : 0 ≤ eNorm x ^ a :=
  Real.rpow_nonneg (eNorm_nonneg x) a

/-! ### The estimates -/

variable (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) (hLodd : Odd L) (hd3 : 3 ≤ d)
  {bbar : ℝ} (hbpos : 0 < bbar) (hb2 : bbar ≤ lbar / 2) (h48 : 48 * C * bbar ≤ 1)
  {bt mt : ℝ → ℝ → ℝ} {β : ℝ} (hsol : SolAt V₀c bbar bt mt β)
include HW hLodd hd3 hbpos hb2 h48 hsol

/-- The basic facts at `h = 0`. -/
theorem zero_facts :
    mt β 0 = 0 ∧ 0 < bt β 0 ∧ bt β 0 < lbar ∧ |s0R V₀c (bt β 0) 0| ≤ 1 / 2 ∧
      |s0R V₀c (bt β 0) 0| ≤ 2 * C * bt β 0 ∧ 0 < β ∧
      c2F V₀c (bt β 0) 0 = (1 + s0R V₀c (bt β 0) 0) / β ∧
      bt β 0 = (1 + s0R V₀c (bt β 0) 0) ^ 2 / β := by
  obtain ⟨-, -, -, -, hβ, -, hm0, -⟩ := hsol 0 le_rfl
  obtain ⟨hb, hbl, -, hs, hs2, -⟩ := sol_facts HW hLodd hd3 hbpos hb2 h48 hsol le_rfl
  rw [hm0] at hβ hs hs2
  have hsC := abs_s0R_le HW.toFlowData hb.le hbl.le le_rfl (V₀c := V₀c)
  have hβp : 0 < β := hβ ▸ betaF_pos hb hs
  have h1 : 0 < 1 + s0R V₀c (bt β 0) 0 := by linarith
  refine ⟨hm0, hb, hbl, hs2, hsC, hβp, ?_, ?_⟩
  · rw [← c2F_eq hb hs, hβ]
  · have h' : (1 + s0R V₀c (bt β 0) 0) ^ 2 / bt β 0 = β := hβ
    rw [eq_div_iff hβp.ne']
    rw [div_eq_iff hb.ne'] at h'
    linarith

/-- `|θ - 1| ≤ (3/2)(|G(0)| + K_Γ λ̄)/β`. -/
theorem est_θ {KΓ : ℝ} (hKΓ : 0 ≤ KΓ)
    (hΓ : ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ‖GamA d L V₀c lbar 0 b₀ - (greenZd d 0 : ℂ)‖ ≤ KΓ * ‖b₀‖) :
    |θh d L V₀c lbar bt mt β 0 - 1| ≤ 3 / 2 * (|greenZd d 0| + KΓ * lbar) / β := by
  obtain ⟨hm0, hb, hbl, hs2, -, hβp, hc2, -⟩ := zero_facts HW hLodd hd3 hbpos hb2 h48 hsol
  have hl := HW.lbar_pos
  have hbn : ‖((bt β 0 : ℝ) : ℂ)‖ ≤ lbar := by
    rw [Complex.norm_real, Real.norm_of_nonneg hb.le]; exact hbl.le
  have hG := hΓ _ hbn
  have hGn : ‖GamA d L V₀c lbar 0 (bt β 0)‖ ≤ |greenZd d 0| + KΓ * lbar := by
    have := norm_le_insert' (GamA d L V₀c lbar 0 (bt β 0)) (greenZd d 0 : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    have := mul_le_mul_of_nonneg_left hbn hKΓ
    linarith
  have hc : 0 ≤ c2F V₀c (bt β 0) 0 ∧ c2F V₀c (bt β 0) 0 ≤ 3 / 2 / β := by
    rw [hc2]
    constructor
    · have : 0 < 1 + s0R V₀c (bt β 0) 0 := by linarith [(abs_le.1 hs2).1]
      positivity
    · exact div_le_div_of_nonneg_right (by linarith [(abs_le.1 hs2).2]) hβp.le
  unfold θh
  rw [hm0]
  have e : (1 - (c2F V₀c (bt β 0) 0 : ℂ) * GamA d L V₀c lbar 0 (bt β 0)).re - 1 =
      -((c2F V₀c (bt β 0) 0 : ℂ) * GamA d L V₀c lbar 0 (bt β 0)).re := by
    simp
  rw [e, abs_neg]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.1]
  calc c2F V₀c (bt β 0) 0 * ‖GamA d L V₀c lbar 0 (bt β 0)‖ ≤
      3 / 2 / β * (|greenZd d 0| + KΓ * lbar) :=
        mul_le_mul hc.2 hGn (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- `|τ₀(x) - (1+s) c_d E(d-2)/β| ≤ K E(d-2+κ')/β`. -/
theorem est_τ {K1 Cg κg : ℝ} (hK1 : 0 ≤ K1) (hCg : 0 ≤ Cg) (hκg : κg ≤ κ) (hκg0 : 0 ≤ κg)
    (hQ1 : ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ∀ x : Zd d, x ≠ 0 →
      ‖Qone d L V₀c lbar 0 b₀ x - (greenZd d x : ℂ)‖ ≤
        K1 * ‖b₀‖ * (supNormZ x : ℝ) ^ (-((d : ℝ) - 2 + κ)))
    (hg : ∀ z : Zd d, z ≠ 0 → |greenZd d z - cd d * eNorm z ^ (2 - (d : ℝ))| ≤
      Cg * eNorm z ^ (2 - (d : ℝ) - κg))
    {x : Zd d} (hx : x ≠ 0) :
    |τh d L V₀c lbar bt mt β x 0 -
        (1 + s0R V₀c (bt β 0) 0) * cd d * eNorm x ^ (-((d : ℝ) - 2)) / β| ≤
      3 / 2 * (K1 * lbar * Real.sqrt d ^ ((d : ℝ) - 2 + κ) + Cg) *
        eNorm x ^ (-((d : ℝ) - 2 + κg)) / β := by
  obtain ⟨hm0, hb, hbl, hs2, -, hβp, hc2, -⟩ := zero_facts HW hLodd hd3 hbpos hb2 h48 hsol
  have hl := HW.lbar_pos
  have hd2 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    linarith
  have hκ := HW.κ_pos
  have hbn : ‖((bt β 0 : ℝ) : ℂ)‖ ≤ lbar := by
    rw [Complex.norm_real, Real.norm_of_nonneg hb.le]; exact hbl.le
  have h1s : 0 < 1 + s0R V₀c (bt β 0) 0 := by linarith [(abs_le.1 hs2).1]
  have h1s' : 1 + s0R V₀c (bt β 0) 0 ≤ 3 / 2 := by linarith [(abs_le.1 hs2).2]
  -- the two errors
  have e1 := hQ1 _ hbn x hx
  have e1' : ‖Qone d L V₀c lbar 0 (bt β 0) x - (greenZd d x : ℂ)‖ ≤
      K1 * lbar * Real.sqrt d ^ ((d : ℝ) - 2 + κ) * eNorm x ^ (-((d : ℝ) - 2 + κg)) := by
    refine e1.trans ?_
    have hr := supNorm_rpow_le hx (a := (d : ℝ) - 2 + κ) (by linarith)
    have hr2 := eNorm_rpow_anti hx (a := (d : ℝ) - 2 + κg) (b := (d : ℝ) - 2 + κ) (by linarith)
    have hsq : 0 ≤ Real.sqrt d ^ ((d : ℝ) - 2 + κ) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    calc K1 * ‖((bt β 0 : ℝ) : ℂ)‖ * (supNormZ x : ℝ) ^ (-((d : ℝ) - 2 + κ))
        ≤ K1 * lbar * (Real.sqrt d ^ ((d : ℝ) - 2 + κ) * eNorm x ^ (-((d : ℝ) - 2 + κ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hbn hK1) hr (by positivity) (by positivity)
      _ ≤ K1 * lbar * (Real.sqrt d ^ ((d : ℝ) - 2 + κ) * eNorm x ^ (-((d : ℝ) - 2 + κg))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr2 hsq) (by positivity)
      _ = _ := by ring
  have e2 := hg x hx
  have e2' : ‖(greenZd d x : ℂ) - ((cd d * eNorm x ^ (-((d : ℝ) - 2)) : ℝ) : ℂ)‖ ≤
      Cg * eNorm x ^ (-((d : ℝ) - 2 + κg)) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      show -((d : ℝ) - 2) = 2 - (d : ℝ) by ring, show -((d : ℝ) - 2 + κg) = 2 - (d : ℝ) - κg by ring]
    exact e2
  unfold τh
  rw [hm0, hc2]
  have e : ((((1 + s0R V₀c (bt β 0) 0) / β : ℝ) : ℂ) * Qone d L V₀c lbar 0 (bt β 0) x).re -
      (1 + s0R V₀c (bt β 0) 0) * cd d * eNorm x ^ (-((d : ℝ) - 2)) / β =
      ((((1 + s0R V₀c (bt β 0) 0) / β : ℝ) : ℂ) * ((Qone d L V₀c lbar 0 (bt β 0) x -
        (greenZd d x : ℂ)) + ((greenZd d x : ℂ) -
          ((cd d * eNorm x ^ (-((d : ℝ) - 2)) : ℝ) : ℂ)))).re := by
    simp only [mul_add, mul_sub, Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul,
      Complex.ofReal_re]
    ring
  rw [e]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hsum := (norm_add_le _ _).trans (add_le_add e1' e2')
  calc (1 + s0R V₀c (bt β 0) 0) / β * ‖(Qone d L V₀c lbar 0 (bt β 0) x - (greenZd d x : ℂ)) +
        ((greenZd d x : ℂ) - ((cd d * eNorm x ^ (-((d : ℝ) - 2)) : ℝ) : ℂ))‖
      ≤ 3 / 2 / β * (K1 * lbar * Real.sqrt d ^ ((d : ℝ) - 2 + κ) *
          eNorm x ^ (-((d : ℝ) - 2 + κg)) + Cg * eNorm x ^ (-((d : ℝ) - 2 + κg))) :=
        mul_le_mul (div_le_div_of_nonneg_right h1s' hβp.le) hsum (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- `|(1+s) c_d - c_d| ≤ (9/2) C c_d / β`. -/
theorem est_c1 (hcd : 0 ≤ cd d) :
    |(1 + s0R V₀c (bt β 0) 0) * cd d - cd d| ≤ 9 / 2 * C * cd d / β := by
  obtain ⟨-, hb, -, hs2, hsC, hβp, -, hbe⟩ := zero_facts HW hLodd hd3 hbpos hb2 h48 hsol
  have hC := HW.C_nonneg
  have hb' : bt β 0 ≤ 9 / 4 / β := by
    rw [hbe]
    refine div_le_div_of_nonneg_right ?_ hβp.le
    have := abs_le.1 hs2
    nlinarith
  rw [show (1 + s0R V₀c (bt β 0) 0) * cd d - cd d = s0R V₀c (bt β 0) 0 * cd d by ring, abs_mul,
    abs_of_nonneg hcd]
  calc |s0R V₀c (bt β 0) 0| * cd d ≤ 2 * C * (9 / 4 / β) * cd d :=
        mul_le_mul_of_nonneg_right (hsC.trans (mul_le_mul_of_nonneg_left hb' (by positivity))) hcd
    _ = _ := by ring

/-- `|Re((1+s)²Λ²) c_d² - c_d²| ≤ K/β`. -/
theorem est_c2 {KΛ : ℝ} (hKΛ : 0 ≤ KΛ)
    (hΛ : ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ‖LamA d L V₀c lbar 0 b₀ - 1‖ ≤ KΛ * ‖b₀‖) (hβ1 : 1 ≤ β) :
    |((1 + s0R V₀c (bt β 0) 0 : ℂ) ^ 2 * LamA d L V₀c lbar 0 (bt β 0) ^ 2).re * cd d ^ 2 -
        cd d ^ 2| ≤
      (9 / 4 * (2 * C * (1 + KΛ * lbar) + KΛ)) * (9 / 4 * (2 * C * (1 + KΛ * lbar) + KΛ) + 2) *
        cd d ^ 2 / β := by
  obtain ⟨-, hb, hbl, hs2, hsC, hβp, -, hbe⟩ := zero_facts HW hLodd hd3 hbpos hb2 h48 hsol
  have hC := HW.C_nonneg
  have hl := HW.lbar_pos
  have hb' : bt β 0 ≤ 9 / 4 / β := by
    rw [hbe]
    refine div_le_div_of_nonneg_right ?_ hβp.le
    have := abs_le.1 hs2
    nlinarith
  have hbn : ‖((bt β 0 : ℝ) : ℂ)‖ ≤ lbar := by
    rw [Complex.norm_real, Real.norm_of_nonneg hb.le]; exact hbl.le
  have hL := hΛ _ hbn
  rw [Complex.norm_real, Real.norm_of_nonneg hb.le] at hL
  set Λ := LamA d L V₀c lbar 0 (bt β 0)
  set s := s0R V₀c (bt β 0) 0
  have hΛn : ‖Λ‖ ≤ 1 + KΛ * lbar := by
    have := norm_le_insert' Λ 1
    rw [norm_one] at this
    have := mul_le_mul_of_nonneg_left hbl.le hKΛ
    linarith
  -- `δ = |(1+s)Λ - 1| ≤ (2C(1+KΛλ̄) + KΛ) b*`
  set D := 2 * C * (1 + KΛ * lbar) + KΛ with hD
  have hδ : ‖(1 + (s : ℂ)) * Λ - 1‖ ≤ D * bt β 0 := by
    have e : (1 + (s : ℂ)) * Λ - 1 = (s : ℂ) * Λ + (Λ - 1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := mul_le_mul hsC hΛn (norm_nonneg _) (by positivity)
    rw [hD]; nlinarith
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hδ' : ‖(1 + (s : ℂ)) * Λ - 1‖ ≤ 9 / 4 * D / β := by
    refine hδ.trans ?_
    calc D * bt β 0 ≤ D * (9 / 4 / β) := mul_le_mul_of_nonneg_left hb' hD0
      _ = _ := by ring
  have hβinv : 9 / 4 * D / β ≤ 9 / 4 * D := by
    rw [div_le_iff₀ hβp]; nlinarith
  have hsq : ‖(1 + (s : ℂ)) ^ 2 * Λ ^ 2 - 1‖ ≤ 9 / 4 * D / β * (9 / 4 * D + 2) := by
    have e : (1 + (s : ℂ)) ^ 2 * Λ ^ 2 - 1 = ((1 + (s : ℂ)) * Λ - 1) * (((1 + (s : ℂ)) * Λ - 1) + 2) := by
      ring
    rw [e, norm_mul]
    refine mul_le_mul hδ' ((norm_add_le _ _).trans ?_) (norm_nonneg _) (by positivity)
    rw [show ‖(2 : ℂ)‖ = 2 by simp]
    linarith
  have e : ((1 + s : ℂ) ^ 2 * Λ ^ 2).re * cd d ^ 2 - cd d ^ 2 =
      ((1 + (s : ℂ)) ^ 2 * Λ ^ 2 - 1).re * cd d ^ 2 := by
    simp only [Complex.sub_re, Complex.one_re]; push_cast; ring
  rw [show ((1 + s0R V₀c (bt β 0) 0 : ℂ)) = 1 + (s : ℂ) by push_cast; rfl, e, abs_mul,
    abs_of_nonneg (sq_nonneg (cd d))]
  have hcd2 : 0 ≤ cd d ^ 2 := sq_nonneg _
  calc |((1 + (s : ℂ)) ^ 2 * Λ ^ 2 - 1).re| * cd d ^ 2 ≤
      (9 / 4 * D / β * (9 / 4 * D + 2)) * cd d ^ 2 :=
        mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans hsq) hcd2
    _ = _ := by ring

/-- `|σ₀(x) + Re((1+s)²Λ²) c_d² E(2(d-2))/β²| ≤ K E(2(d-2)+κ')/β²`. -/
theorem est_σ {K2 KΛ Cg CG κg : ℝ} (hK2 : 0 ≤ K2) (hKΛ : 0 ≤ KΛ) (hCg : 0 ≤ Cg)
    (hCG : 0 ≤ CG) (hκg : κg ≤ κ) (hκg0 : 0 ≤ κg)
    (hQ2 : ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ∀ x : Zd d, x ≠ 0 →
      ‖Qtwo d L V₀c lbar 0 b₀ x + LamA d L V₀c lbar 0 b₀ ^ 2 * (greenZd d x : ℂ) ^ 2‖ ≤
        K2 * ‖b₀‖ * (supNormZ x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ)))
    (hΛ : ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ‖LamA d L V₀c lbar 0 b₀ - 1‖ ≤ KΛ * ‖b₀‖)
    (hg : ∀ z : Zd d, z ≠ 0 → |greenZd d z - cd d * eNorm z ^ (2 - (d : ℝ))| ≤
      Cg * eNorm z ^ (2 - (d : ℝ) - κg))
    (hG : ∀ z : Zd d, z ≠ 0 → |greenZd d z| ≤ CG * eNorm z ^ (-((d : ℝ) - 2)))
    (hcd : 0 ≤ cd d) {x : Zd d} (hx : x ≠ 0) :
    |σh d L V₀c lbar bt mt β x 0 +
        ((1 + s0R V₀c (bt β 0) 0 : ℂ) ^ 2 * LamA d L V₀c lbar 0 (bt β 0) ^ 2).re * cd d ^ 2 *
          eNorm x ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2| ≤
      9 / 4 * (K2 * lbar * Real.sqrt d ^ (2 * ((d : ℝ) - 2) + κ) +
        (1 + KΛ * lbar) ^ 2 * (Cg * (CG + cd d))) *
        eNorm x ^ (-(2 * ((d : ℝ) - 2) + κg)) / β ^ 2 := by
  obtain ⟨hm0, hb, hbl, hs2, -, hβp, hc2, -⟩ := zero_facts HW hLodd hd3 hbpos hb2 h48 hsol
  have hl := HW.lbar_pos
  have hd2 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
    linarith
  have hκ := HW.κ_pos
  have hbn : ‖((bt β 0 : ℝ) : ℂ)‖ ≤ lbar := by
    rw [Complex.norm_real, Real.norm_of_nonneg hb.le]; exact hbl.le
  have h1s : 0 < 1 + s0R V₀c (bt β 0) 0 := by linarith [(abs_le.1 hs2).1]
  have h1s' : 1 + s0R V₀c (bt β 0) 0 ≤ 3 / 2 := by linarith [(abs_le.1 hs2).2]
  set Λ := LamA d L V₀c lbar 0 (bt β 0)
  set s := s0R V₀c (bt β 0) 0
  set G := greenZd d x
  set e := eNorm x
  have he1 := one_le_eNorm hx
  have hL := hΛ _ hbn
  rw [Complex.norm_real, Real.norm_of_nonneg hb.le] at hL
  have hΛn : ‖Λ‖ ≤ 1 + KΛ * lbar := by
    have := norm_le_insert' Λ 1
    rw [norm_one] at this
    have := mul_le_mul_of_nonneg_left hbl.le hKΛ
    linarith
  -- errors
  have r1 : ‖Qtwo d L V₀c lbar 0 (bt β 0) x + Λ ^ 2 * (G : ℂ) ^ 2‖ ≤
      K2 * lbar * Real.sqrt d ^ (2 * ((d : ℝ) - 2) + κ) * e ^ (-(2 * ((d : ℝ) - 2) + κg)) := by
    refine (hQ2 _ hbn x hx).trans ?_
    have hr := supNorm_rpow_le hx (a := 2 * ((d : ℝ) - 2) + κ) (by linarith)
    have hr2 := eNorm_rpow_anti hx (a := 2 * ((d : ℝ) - 2) + κg) (b := 2 * ((d : ℝ) - 2) + κ)
      (by linarith)
    have hsq : 0 ≤ Real.sqrt d ^ (2 * ((d : ℝ) - 2) + κ) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    calc K2 * ‖((bt β 0 : ℝ) : ℂ)‖ * (supNormZ x : ℝ) ^ (-(2 * ((d : ℝ) - 2) + κ))
        ≤ K2 * lbar * (Real.sqrt d ^ (2 * ((d : ℝ) - 2) + κ) * e ^ (-(2 * ((d : ℝ) - 2) + κ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hbn hK2) hr (by positivity) (by positivity)
      _ ≤ K2 * lbar * (Real.sqrt d ^ (2 * ((d : ℝ) - 2) + κ) * e ^ (-(2 * ((d : ℝ) - 2) + κg))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr2 hsq) (by positivity)
      _ = _ := by ring
  have hmain : e ^ (-((d : ℝ) - 2)) * e ^ (-((d : ℝ) - 2)) = e ^ (-(2 * ((d : ℝ) - 2))) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have hmain2 : e ^ (2 - (d : ℝ) - κg) * e ^ (-((d : ℝ) - 2)) = e ^ (-(2 * ((d : ℝ) - 2) + κg)) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have r2 : |G ^ 2 - cd d ^ 2 * e ^ (-(2 * ((d : ℝ) - 2)))| ≤
      Cg * (CG + cd d) * e ^ (-(2 * ((d : ℝ) - 2) + κg)) := by
    have hg1 : |G - cd d * e ^ (-((d : ℝ) - 2))| ≤ Cg * e ^ (2 - (d : ℝ) - κg) := by
      have h := hg x hx
      rw [show (2 : ℝ) - d = -((d : ℝ) - 2) by ring] at h
      rw [show (2 : ℝ) - d - κg = -((d : ℝ) - 2) - κg by ring]
      exact h
    have hG1 := hG x hx
    have hsum : |G + cd d * e ^ (-((d : ℝ) - 2))| ≤ (CG + cd d) * e ^ (-((d : ℝ) - 2)) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hcd, abs_of_nonneg (eNorm_rpow_nonneg x _)]
      linarith
    have e' : G ^ 2 - cd d ^ 2 * e ^ (-(2 * ((d : ℝ) - 2))) =
        (G - cd d * e ^ (-((d : ℝ) - 2))) * (G + cd d * e ^ (-((d : ℝ) - 2))) := by
      rw [← hmain]; ring
    rw [e', abs_mul]
    calc |G - cd d * e ^ (-((d : ℝ) - 2))| * |G + cd d * e ^ (-((d : ℝ) - 2))| ≤
        (Cg * e ^ (2 - (d : ℝ) - κg)) * ((CG + cd d) * e ^ (-((d : ℝ) - 2))) :=
          mul_le_mul hg1 hsum (abs_nonneg _) (by positivity)
      _ = Cg * (CG + cd d) * (e ^ (2 - (d : ℝ) - κg) * e ^ (-((d : ℝ) - 2))) := by ring
      _ = _ := by rw [hmain2]
  -- assemble
  unfold σh
  rw [hm0, hc2]
  have hkey : (((1 + s) / β : ℝ) : ℂ) ^ 2 * Qtwo d L V₀c lbar 0 (bt β 0) x +
      ((1 + (s : ℂ)) ^ 2 * Λ ^ 2) * (((cd d ^ 2 * e ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2 : ℝ) : ℂ)) =
      (((1 + s) / β : ℝ) : ℂ) ^ 2 * ((Qtwo d L V₀c lbar 0 (bt β 0) x + Λ ^ 2 * (G : ℂ) ^ 2) -
        Λ ^ 2 * (((G ^ 2 - cd d ^ 2 * e ^ (-(2 * ((d : ℝ) - 2))) : ℝ) : ℂ))) := by
    have hβ0 : (β : ℂ) ≠ 0 := by exact_mod_cast hβp.ne'
    push_cast
    field_simp
    ring
  have hre : ((((1 + s) / β : ℝ) : ℂ) ^ 2 * Qtwo d L V₀c lbar 0 (bt β 0) x).re +
      ((1 + (s : ℂ)) ^ 2 * Λ ^ 2).re * cd d ^ 2 * e ^ (-(2 * ((d : ℝ) - 2))) / β ^ 2 =
      ((((1 + s) / β : ℝ) : ℂ) ^ 2 * ((Qtwo d L V₀c lbar 0 (bt β 0) x + Λ ^ 2 * (G : ℂ) ^ 2) -
        Λ ^ 2 * (((G ^ 2 - cd d ^ 2 * e ^ (-(2 * ((d : ℝ) - 2))) : ℝ) : ℂ)))).re := by
    rw [← hkey, Complex.add_re, Complex.re_mul_ofReal]
    ring
  rw [show ((1 + s0R V₀c (bt β 0) 0 : ℂ)) = 1 + (s : ℂ) by push_cast; rfl, hre]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hn : ‖(Qtwo d L V₀c lbar 0 (bt β 0) x + Λ ^ 2 * (G : ℂ) ^ 2) -
      Λ ^ 2 * (((G ^ 2 - cd d ^ 2 * e ^ (-(2 * ((d : ℝ) - 2))) : ℝ) : ℂ))‖ ≤
      K2 * lbar * Real.sqrt d ^ (2 * ((d : ℝ) - 2) + κ) * e ^ (-(2 * ((d : ℝ) - 2) + κg)) +
        (1 + KΛ * lbar) ^ 2 * (Cg * (CG + cd d) * e ^ (-(2 * ((d : ℝ) - 2) + κg))) := by
    refine (norm_sub_le _ _).trans (add_le_add r1 ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hΛn 2) r2 (abs_nonneg _) (by positivity)
  have hc : ((1 + s) / β) ^ 2 ≤ 9 / 4 / β ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  calc ((1 + s) / β) ^ 2 * ‖(Qtwo d L V₀c lbar 0 (bt β 0) x + Λ ^ 2 * (G : ℂ) ^ 2) -
        Λ ^ 2 * (((G ^ 2 - cd d ^ 2 * e ^ (-(2 * ((d : ℝ) - 2))) : ℝ) : ℂ))‖
      ≤ 9 / 4 / β ^ 2 * (K2 * lbar * Real.sqrt d ^ (2 * ((d : ℝ) - 2) + κ) *
          e ^ (-(2 * ((d : ℝ) - 2) + κg)) + (1 + KΛ * lbar) ^ 2 * (Cg * (CG + cd d) *
            e ^ (-(2 * ((d : ℝ) - 2) + κg)))) :=
        mul_le_mul hc hn (norm_nonneg _) (by positivity)
    _ = _ := by ring

end

end Ward
