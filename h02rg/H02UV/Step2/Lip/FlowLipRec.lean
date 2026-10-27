import Step2.Lip.FlowLipInd

/-!
# The recursion of the errors in closed form (Lipschitz bounds, part 22)

Pure real-number lemmas turning the one-step error bounds (`ev_succ_le`, `eW_succ_le`,
`ew_succ_le`, `thetaH_le`) into the linear recursion of `err_rec`, with explicit constants.
-/

namespace Step2

noncomputable section

/-- The `M` coefficient of `aIn`-type bounds. -/
def kX (ℓ : ℝ) : ℝ := (cM : ℝ) * ℓ ^ 2 + 5 * ℓ ^ 4 + 32 * ℓ ^ 6
def kc1 (ℓ cmu : ℝ) : ℝ := 2 * (cM : ℝ) * ℓ ^ 2 + 64 * cmu * ℓ ^ 6
def kc2 (ℓ cmu : ℝ) : ℝ := 36 * cmu * ℓ ^ 4

/-- The constant `a₀` of the coupling recursion. -/
def ka0 (ℓ β : ℝ) : ℝ := 8 * β * (1 + Real.exp 1 + kX ℓ) + 3 * ℓ ^ 2 / 16 * (8 / 7 + 8 * ℓ ^ 2)

/-- The constants of the small terms of the coupling recursion. -/
def kEv (ℓ β cmu cTh : ℝ) : ℝ := 8 * β * (kc1 ℓ cmu + cTh) + 3 * ℓ ^ 4 * cmu
def kEw (ℓ β cmu : ℝ) : ℝ := 8 * β * kc2 ℓ cmu + 2 * ℓ ^ 2 * cmu
def kEV (ℓ β Λ0 : ℝ) : ℝ := 128 * β * Λ0 / ℓ ^ 2 + 6 * Λ0

theorem kX_nonneg (ℓ : ℝ) : 0 ≤ kX ℓ := by
  unfold kX; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity

/-- The bound on `dn`. -/
theorem dn_bound {dn dμ eζ ew ev M ℓ cmu ε : ℝ} (hcmu : 0 ≤ cmu) (hε : 0 ≤ ε)
    (hdμ : dμ ≤ M) (hζ : eζ ≤ ev)
    (hdn : dn ≤ 4 * (ℓ ^ 2 * dμ + cmu * ε * (2 * ℓ ^ 2 * eζ + 9 / 8 * ew))) :
    dn ≤ 4 * ℓ ^ 2 * M + 8 * cmu * ℓ ^ 2 * ε * ev + 9 / 2 * cmu * ε * ew := by
  have h1 : ℓ ^ 2 * dμ ≤ ℓ ^ 2 * M := mul_le_mul_of_nonneg_left hdμ (by positivity)
  have h2 : cmu * ε * (2 * ℓ ^ 2 * eζ) ≤ cmu * ε * (2 * ℓ ^ 2 * ev) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  nlinarith

/-- The bound on `aIn`-type quantities. -/
theorem X_bound {X dμ dg dn ev ew M ℓ cmu ε : ℝ} (hcmu : 0 ≤ cmu) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hev : 0 ≤ ev) (hew : 0 ≤ ew) (hdg : dg ≤ M) (hdμ : dμ ≤ M)
    (hdn' : dn ≤ 4 * ℓ ^ 2 * M + 8 * cmu * ℓ ^ 2 * ε * ev + 9 / 2 * cmu * ε * ew)
    (hX : X ≤ (cM : ℝ) * ℓ ^ 2 * dμ + 5 * ℓ ^ 4 * dg + 8 * ℓ ^ 4 * dn + 2 * cM * ℓ ^ 2 * ev) :
    X ≤ kX ℓ * M + kc1 ℓ cmu * ev + kc2 ℓ cmu * ew := by
  have hM' : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  unfold kX kc1 kc2
  have a1 : (cM : ℝ) * ℓ ^ 2 * dμ ≤ cM * ℓ ^ 2 * M := mul_le_mul_of_nonneg_left hdμ (by positivity)
  have a2 : 5 * ℓ ^ 4 * dg ≤ 5 * ℓ ^ 4 * M := mul_le_mul_of_nonneg_left hdg (by positivity)
  have a3 : 8 * ℓ ^ 4 * dn ≤ 8 * ℓ ^ 4 * (4 * ℓ ^ 2 * M + 8 * cmu * ℓ ^ 2 * ε * ev +
      9 / 2 * cmu * ε * ew) := mul_le_mul_of_nonneg_left hdn' (by positivity)
  have a4 : 64 * cmu * ℓ ^ 6 * ev * ε ≤ 64 * cmu * ℓ ^ 6 * ev :=
    mul_le_of_le_one_right (by positivity) hε1
  have a5 : 36 * cmu * ℓ ^ 4 * ew * ε ≤ 36 * cmu * ℓ ^ 4 * ew :=
    mul_le_of_le_one_right (by positivity) hε1
  have e1 : 8 * ℓ ^ 4 * (4 * ℓ ^ 2 * M + 8 * cmu * ℓ ^ 2 * ε * ev + 9 / 2 * cmu * ε * ew) =
      32 * ℓ ^ 6 * M + 64 * cmu * ℓ ^ 6 * ev * ε + 36 * cmu * ℓ ^ 4 * ew * ε := by ring
  linarith

/-- **The coupling recursion.** -/
theorem ev_rec {ev' Θ G γ ℓΔ2 dx dg dμ dn eW ev ew eζ M V ℓ β cmu cTh Λ0 e ε : ℝ}
    (hℓ : 0 < ℓ) (hβ : 0 ≤ β) (hcmu : 0 ≤ cmu) (hcTh : 0 ≤ cTh) (hΛ0 : 0 ≤ Λ0)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hev : 0 ≤ ev) (hew : 0 ≤ ew)
    (hdx : dx ≤ M) (hdg : dg ≤ M) (hdμ : dμ ≤ M) (hζ : eζ ≤ ev)
    (hdn : dn ≤ 4 * (ℓ ^ 2 * dμ + cmu * ε * (2 * ℓ ^ 2 * eζ + 9 / 8 * ew)))
    (hΔ : ℓΔ2 ≤ Λ0 * (V * M)) (hΔ0 : 0 ≤ ℓΔ2)
    (hΘ : Θ ≤ (1 + Real.exp 1) * dx + eW + e * ((cM : ℝ) * ℓ ^ 2 * dμ + 5 * ℓ ^ 4 * dg +
      8 * ℓ ^ 4 * dn + 2 * cM * ℓ ^ 2 * ev) + ε ^ 2 * cTh * ev + 16 * e ^ 2 * ℓΔ2 / ℓ ^ 2)
    (hG : G ≤ 8 / 7 * dg + 2 * dn) (hγ : γ ≤ 2 * ε) (hγ0 : 0 ≤ γ)
    (hev' : ev' ≤ 8 * β * Θ + (3 * (ℓ / 4) ^ 2 * G + 3 * γ * ℓΔ2)) :
    ev' ≤ ka0 ℓ β * M + 8 * β * eW + (e + ε) * (kEv ℓ β cmu cTh * ev + kEw ℓ β cmu * ew +
      kEV ℓ β Λ0 * (V * M)) := by
  have hdn' := dn_bound hcmu hε hdμ hζ hdn
  obtain ⟨X, hXd⟩ : ∃ X, X = (cM : ℝ) * ℓ ^ 2 * dμ + 5 * ℓ ^ 4 * dg + 8 * ℓ ^ 4 * dn +
    2 * cM * ℓ ^ 2 * ev := ⟨_, rfl⟩
  rw [← hXd] at hΘ
  have hX := X_bound hcmu hε hε1 hev hew hdg hdμ hdn' hXd.le
  unfold ka0
  have hE1 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  generalize Real.exp 1 = E1 at *
  have hk1 : 0 ≤ kc1 ℓ cmu := by unfold kc1; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hk2 : 0 ≤ kc2 ℓ cmu := by unfold kc2; positivity
  have hkX := kX_nonneg ℓ
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hS : 0 ≤ e + ε := by linarith
  -- e X
  have t1 : e * X ≤ kX ℓ * M + (e + ε) * (kc1 ℓ cmu * ev + kc2 ℓ cmu * ew) := by
    have h1 := mul_le_mul_of_nonneg_left hX he
    have h2 : e * (kX ℓ * M) ≤ kX ℓ * M := mul_le_of_le_one_left (by positivity) he1
    have h3 : e * (kc1 ℓ cmu * ev + kc2 ℓ cmu * ew) ≤ (e + ε) * (kc1 ℓ cmu * ev + kc2 ℓ cmu * ew) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e1 : e * (kX ℓ * M + kc1 ℓ cmu * ev + kc2 ℓ cmu * ew) =
        e * (kX ℓ * M) + e * (kc1 ℓ cmu * ev + kc2 ℓ cmu * ew) := by ring
    linarith only [h1, h2, h3, e1]
  have t2 : ε ^ 2 * cTh * ev ≤ (e + ε) * (cTh * ev) := by
    have h0 : ε ^ 2 ≤ e + ε := by nlinarith
    have := mul_le_mul_of_nonneg_right h0 (mul_nonneg hcTh hev)
    linarith only [this, show ε ^ 2 * cTh * ev = ε ^ 2 * (cTh * ev) by ring]
  have t3 : 16 * e ^ 2 * ℓΔ2 / ℓ ^ 2 ≤ (e + ε) * (16 * Λ0 / ℓ ^ 2 * (V * M)) := by
    have h1 : e ^ 2 ≤ e + ε := by nlinarith
    have h2 : 16 * e ^ 2 * ℓΔ2 / ℓ ^ 2 = e ^ 2 * (16 / ℓ ^ 2 * ℓΔ2) := by ring
    have h3 : 16 / ℓ ^ 2 * ℓΔ2 ≤ 16 * Λ0 / ℓ ^ 2 * (V * M) := by
      have : 16 / ℓ ^ 2 * ℓΔ2 ≤ 16 / ℓ ^ 2 * (Λ0 * (V * M)) :=
        mul_le_mul_of_nonneg_left hΔ (by positivity)
      linarith [show 16 / ℓ ^ 2 * (Λ0 * (V * M)) = 16 * Λ0 / ℓ ^ 2 * (V * M) by ring]
    rw [h2]
    calc e ^ 2 * (16 / ℓ ^ 2 * ℓΔ2) ≤ (e + ε) * (16 / ℓ ^ 2 * ℓΔ2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hS
  have t4 : 3 * (ℓ / 4) ^ 2 * G ≤ 3 * ℓ ^ 2 / 16 * (8 / 7 + 8 * ℓ ^ 2) * M +
      (e + ε) * (3 * ℓ ^ 4 * cmu * ev + 2 * ℓ ^ 2 * cmu * ew) := by
    have hG' : G ≤ 8 / 7 * M + 2 * (4 * ℓ ^ 2 * M + 8 * cmu * ℓ ^ 2 * ε * ev +
        9 / 2 * cmu * ε * ew) := by linarith
    have hc : 0 ≤ 3 * (ℓ / 4) ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hG' hc
    have e1 : 3 * (ℓ / 4) ^ 2 * (8 / 7 * M + 2 * (4 * ℓ ^ 2 * M + 8 * cmu * ℓ ^ 2 * ε * ev +
        9 / 2 * cmu * ε * ew)) = 3 * ℓ ^ 2 / 16 * (8 / 7 + 8 * ℓ ^ 2) * M +
        ε * (3 * ℓ ^ 4 * cmu * ev + 27 / 16 * ℓ ^ 2 * cmu * ew) := by ring
    have h2 : ε * (3 * ℓ ^ 4 * cmu * ev + 27 / 16 * ℓ ^ 2 * cmu * ew) ≤
        (e + ε) * (3 * ℓ ^ 4 * cmu * ev + 2 * ℓ ^ 2 * cmu * ew) := by
      have : 3 * ℓ ^ 4 * cmu * ev + 27 / 16 * ℓ ^ 2 * cmu * ew ≤
          3 * ℓ ^ 4 * cmu * ev + 2 * ℓ ^ 2 * cmu * ew := by
        have : 0 ≤ ℓ ^ 2 * cmu * ew := by positivity
        linarith
      calc ε * (3 * ℓ ^ 4 * cmu * ev + 27 / 16 * ℓ ^ 2 * cmu * ew)
          ≤ ε * (3 * ℓ ^ 4 * cmu * ev + 2 * ℓ ^ 2 * cmu * ew) :=
            mul_le_mul_of_nonneg_left this hε
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have t5 : 3 * γ * ℓΔ2 ≤ (e + ε) * (6 * Λ0 * (V * M)) := by
    have h1 : 3 * γ * ℓΔ2 ≤ 3 * (2 * ε) * (Λ0 * (V * M)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hγ (by norm_num)) hΔ hΔ0 (by positivity)
    have h2 : 3 * (2 * ε) * (Λ0 * (V * M)) ≤ (e + ε) * (6 * Λ0 * (V * M)) := by
      have h0 : 0 ≤ 6 * Λ0 * (V * M) := by positivity
      have := mul_le_mul_of_nonneg_right (show ε ≤ e + ε by linarith) h0
      linarith only [this, show 3 * (2 * ε) * (Λ0 * (V * M)) = ε * (6 * Λ0 * (V * M)) by ring]
    linarith only [h1, h2]
  have hdx' : (1 + E1) * dx ≤ (1 + E1) * M :=
    mul_le_mul_of_nonneg_left hdx (by positivity)
  have hΘ' : Θ ≤ (1 + E1) * M + eW + (kX ℓ * M + (e + ε) * (kc1 ℓ cmu * ev +
      kc2 ℓ cmu * ew)) + (e + ε) * (cTh * ev) + (e + ε) * (16 * Λ0 / ℓ ^ 2 * (V * M)) := by
    linarith only [hΘ, hdx', t1, t2, t3]
  have h8 := mul_le_mul_of_nonneg_left hΘ' (by positivity : (0 : ℝ) ≤ 8 * β)
  unfold kEv kEw kEV
  have e2 : 8 * β * ((1 + E1) * M + eW + (kX ℓ * M + (e + ε) * (kc1 ℓ cmu * ev +
      kc2 ℓ cmu * ew)) + (e + ε) * (cTh * ev) + (e + ε) * (16 * Λ0 / ℓ ^ 2 * (V * M))) =
      8 * β * (1 + E1 + kX ℓ) * M + 8 * β * eW + (e + ε) * ((8 * β * (kc1 ℓ cmu + cTh)) * ev +
        8 * β * kc2 ℓ cmu * ew + 128 * β * Λ0 / ℓ ^ 2 * (V * M)) := by ring
  have e3 : (e + ε) * ((8 * β * (kc1 ℓ cmu + cTh) + 3 * ℓ ^ 4 * cmu) * ev +
      (8 * β * kc2 ℓ cmu + 2 * ℓ ^ 2 * cmu) * ew + (128 * β * Λ0 / ℓ ^ 2 + 6 * Λ0) * (V * M)) =
      (e + ε) * ((8 * β * (kc1 ℓ cmu + cTh)) * ev + 8 * β * kc2 ℓ cmu * ew +
        128 * β * Λ0 / ℓ ^ 2 * (V * M)) + (e + ε) * (3 * ℓ ^ 4 * cmu * ev + 2 * ℓ ^ 2 * cmu * ew) +
        (e + ε) * (6 * Λ0 * (V * M)) := by ring
  rw [e3]
  linarith only [h8, e2, t4, t5, hev']

/-- The constants of the `𝒲^lin` recursion. -/
def kWM (ℓ C₂ : ℝ) : ℝ := 16 * C₂ * kX ℓ
def kWv (ℓ C₂ κW cw cmu : ℝ) : ℝ := 16 * C₂ * kc1 ℓ cmu + 224 * κW * cw
def kWw (ℓ C₂ cmu : ℝ) : ℝ := 16 * C₂ * kc2 ℓ cmu
def kWV (ℓ C₂ κW cw Λ0 : ℝ) : ℝ := 256 * C₂ * Λ0 / ℓ ^ 2 + 128 * κW * (cw + 1) * Λ0 / ℓ ^ 2

/-- **The `𝒲^lin` recursion.** -/
theorem eW_rec {eW' aIn bW ℓΔ2 dg dμ dn eW ev ew eζ M V ℓ C₂ κW cw cmu Λ0 e ε : ℝ}
    (hℓ : 0 < ℓ) (hC₂ : 0 ≤ C₂) (hκW : 0 ≤ κW) (hcw : 0 ≤ cw) (hcmu : 0 ≤ cmu) (hΛ0 : 0 ≤ Λ0)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hev : 0 ≤ ev) (hew : 0 ≤ ew) (hdg : dg ≤ M) (hdμ : dμ ≤ M) (hζ : eζ ≤ ev)
    (hdn : dn ≤ 4 * (ℓ ^ 2 * dμ + cmu * ε * (2 * ℓ ^ 2 * eζ + 9 / 8 * ew)))
    (hΔ : ℓΔ2 ≤ Λ0 * (V * M)) (hΔ0 : 0 ≤ ℓΔ2)
    (ha : aIn ≤ (cM : ℝ) * ℓ ^ 2 * dμ + 5 * ℓ ^ 4 * dg + 8 * ℓ ^ 4 * dn + 2 * cM * ℓ ^ 2 * ev)
    (hbW : bW ≤ eW + 28 * cw * ε ^ 2 * ev)
    (hW : eW' ≤ 16 * C₂ * (e * aIn + 16 * e ^ 2 * ℓΔ2 / ℓ ^ 2) +
      8 * κW * (bW + 16 * ((cw + 1) * ε ^ 2) * ℓΔ2 / ℓ ^ 2)) :
    eW' ≤ 8 * κW * eW + (e + ε) * (kWM ℓ C₂ * M + kWv ℓ C₂ κW cw cmu * ev + kWw ℓ C₂ cmu * ew +
      kWV ℓ C₂ κW cw Λ0 * (V * M)) := by
  have hdn' := dn_bound hcmu hε hdμ hζ hdn
  have hX := X_bound hcmu hε hε1 hev hew hdg hdμ hdn' ha
  have hk1 : 0 ≤ kc1 ℓ cmu := by unfold kc1; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hk2 : 0 ≤ kc2 ℓ cmu := by unfold kc2; positivity
  have hkX := kX_nonneg ℓ
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hS : e ≤ e + ε := by linarith
  have hS0 : 0 ≤ e + ε := by linarith
  have t1 : e * aIn ≤ (e + ε) * (kX ℓ * M + kc1 ℓ cmu * ev + kc2 ℓ cmu * ew) :=
    (mul_le_mul_of_nonneg_left hX he).trans (mul_le_mul_of_nonneg_right hS (by positivity))
  have hε2 : ε ^ 2 ≤ e + ε := by nlinarith
  have hΔ' : ℓΔ2 / ℓ ^ 2 ≤ Λ0 / ℓ ^ 2 * (V * M) := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hℓ2]; exact hΔ
  have hΔ0' : 0 ≤ ℓΔ2 / ℓ ^ 2 := by positivity
  have t2 : 16 * e ^ 2 * ℓΔ2 / ℓ ^ 2 ≤ (e + ε) * (16 * e * (Λ0 / ℓ ^ 2 * (V * M))) := by
    have : 16 * e ^ 2 * ℓΔ2 / ℓ ^ 2 = e * (16 * e * (ℓΔ2 / ℓ ^ 2)) := by ring
    rw [this]
    exact mul_le_mul hS (mul_le_mul_of_nonneg_left hΔ' (by positivity)) (by positivity) hS0
  have t3 : 28 * cw * ε ^ 2 * ev ≤ (e + ε) * (28 * cw * ev) := by
    have := mul_le_mul_of_nonneg_right hε2 (by positivity : (0 : ℝ) ≤ 28 * cw * ev)
    linarith only [this, show 28 * cw * ε ^ 2 * ev = ε ^ 2 * (28 * cw * ev) by ring]
  have t4 : 16 * ((cw + 1) * ε ^ 2) * ℓΔ2 / ℓ ^ 2 ≤ (e + ε) * (16 * (cw + 1) * (Λ0 / ℓ ^ 2 * (V * M))) := by
    have : 16 * ((cw + 1) * ε ^ 2) * ℓΔ2 / ℓ ^ 2 = ε ^ 2 * (16 * (cw + 1) * (ℓΔ2 / ℓ ^ 2)) := by ring
    rw [this]
    exact mul_le_mul hε2 (mul_le_mul_of_nonneg_left hΔ' (by positivity)) (by positivity) hS0
  have t2' : (e + ε) * (16 * e * (Λ0 / ℓ ^ 2 * (V * M))) ≤ (e + ε) * (16 * (Λ0 / ℓ ^ 2 * (V * M))) := by
    have h0 : 0 ≤ Λ0 / ℓ ^ 2 * (V * M) := by positivity
    have : 16 * e * (Λ0 / ℓ ^ 2 * (V * M)) ≤ 16 * (Λ0 / ℓ ^ 2 * (V * M)) := by nlinarith
    exact mul_le_mul_of_nonneg_left this hS0
  have hW1 := mul_le_mul_of_nonneg_left (add_le_add t1 (t2.trans t2'))
    (by positivity : (0 : ℝ) ≤ 16 * C₂)
  have hW2 := mul_le_mul_of_nonneg_left (add_le_add (hbW.trans (add_le_add_right t3 eW)) t4)
    (by positivity : (0 : ℝ) ≤ 8 * κW)
  unfold kWM kWv kWw kWV
  have e1 : 16 * C₂ * ((e + ε) * (kX ℓ * M + kc1 ℓ cmu * ev + kc2 ℓ cmu * ew) +
      (e + ε) * (16 * (Λ0 / ℓ ^ 2 * (V * M)))) + 8 * κW * (eW + (e + ε) * (28 * cw * ev) +
      (e + ε) * (16 * (cw + 1) * (Λ0 / ℓ ^ 2 * (V * M)))) =
      8 * κW * eW + (e + ε) * (16 * C₂ * kX ℓ * M + (16 * C₂ * kc1 ℓ cmu + 224 * κW * cw) * ev +
        16 * C₂ * kc2 ℓ cmu * ew + (256 * C₂ * Λ0 / ℓ ^ 2 + 128 * κW * (cw + 1) * Λ0 / ℓ ^ 2) *
          (V * M)) := by ring
  linarith only [hW, hW1, hW2, e1]


/-- **The zero-mode recursion.** -/
theorem ew_rec {ew' dnW eζ ev ew ℓΔ2 M V ℓ Λ0 Lr : ℝ} (hLr : 0 < Lr) (hΛ0 : 0 ≤ Λ0)
    (hev : 0 ≤ ev) (hew : 0 ≤ ew) (hM : 0 ≤ M) (hV : 0 ≤ V) (hζ : eζ ≤ ev)
    (hdnW : dnW ≤ 2 * ℓ ^ 2 * eζ + 9 / 8 * ew) (hΔ : ℓΔ2 ≤ Λ0 * (V * M))
    (hw : ew' ≤ dnW / Lr ^ 2 + 9 * ℓΔ2) :
    ew' ≤ 9 / (8 * Lr ^ 2) * ew + (2 * ℓ ^ 2 / Lr ^ 2 + 9 * Λ0) * (ev + V * M) := by
  have hL2 : 0 < Lr ^ 2 := by positivity
  have hd : dnW ≤ 2 * ℓ ^ 2 * ev + 9 / 8 * ew := by
    have : 2 * ℓ ^ 2 * eζ ≤ 2 * ℓ ^ 2 * ev := mul_le_mul_of_nonneg_left hζ (by positivity)
    linarith
  have h1 : dnW / Lr ^ 2 ≤ (2 * ℓ ^ 2 * ev + 9 / 8 * ew) / Lr ^ 2 := by
    rw [div_le_div_iff_of_pos_right hL2]; exact hd
  have e1 : (2 * ℓ ^ 2 * ev + 9 / 8 * ew) / Lr ^ 2 = 9 / (8 * Lr ^ 2) * ew + 2 * ℓ ^ 2 / Lr ^ 2 * ev := by
    field_simp; ring
  have h2 : 2 * ℓ ^ 2 / Lr ^ 2 * ev ≤ 2 * ℓ ^ 2 / Lr ^ 2 * (ev + V * M) :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hV hM]) (by positivity)
  have h3 : 9 * ℓΔ2 ≤ 9 * Λ0 * (ev + V * M) := by
    have : Λ0 * (V * M) ≤ Λ0 * (ev + V * M) := mul_le_mul_of_nonneg_left (by linarith) hΛ0
    linarith
  have e2 : (2 * ℓ ^ 2 / Lr ^ 2 + 9 * Λ0) * (ev + V * M) =
      2 * ℓ ^ 2 / Lr ^ 2 * (ev + V * M) + 9 * Λ0 * (ev + V * M) := by ring
  linarith

end

end Step2
