import Step2.Last.FlowGlueG

/-!
# The step at `j = N - 2` along a regular history

`glue_core`: the bounds on the output of one step under `ValidAtL` (so at `j = N - 2`), from
`Last.StepBounds` and `GStepBound`, for inputs with the a priori bounds (`APB`) and in `D_ε`:

* `|z'/Z'|, |y'/Z'| ≤ c_z ǧ`, `|ν' - L² μ| ≤ c_ν ǧ` (`cNuL`);
* `‖W^lin'‖ ≤ c_w ǧ²`, `‖D'‖ ≤ c_D ǧ²` (`cDL`), `‖K'‖ ≤ c_K ǧ³` (`cKL`), at the output field
  scale;
* `|ǧ'| ≤ 3 ǧ`, `Re ǧ' ≥ ǧ/12` (the latter if `c_E(C_q^g, …) ε ≤ ℓ²/24`).

`glue_step`: the same along a regular history at `j = N_h` (`histOut R N_h t`), with the a priori
bounds from `apriori`. `admissible_InDh_rg`: admissible trajectories of `rgData` are regular.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- `Last.StepBounds` is monotone in `C₀` and `η` (copy of `StepBounds.mono`). -/
theorem Last.StepBounds.mono {L : ℕ} [NeZero L] {A C₀ η εs CK C₂ CD Cq Cl cS C₀' η' : ℝ}
    (h : Last.StepBounds L A C₀ η εs CK C₂ CD Cq Cl cS) (hC0 : 0 ≤ C₀) (hC : C₀ ≤ C₀')
    (hη : η' ≤ η) (hA : 2 ≤ A) :
    Last.StepBounds L A C₀' η' εs CK C₂ CD Cq Cl cS := by
  intro N R j hV st hI g μ D K hD hK hm hg ηz h1 h2 h3 h4 wl dd k r hwl hdd hk hW hDn hKn v hv hr
    hrε hkε
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ :=
    h N R j hV st hI g μ D K hD hK hm hg ηz h1 h2 h3 h4 wl dd k r hwl hdd hk hW hDn hKn hv hr hrε hkε
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hdiv : C₀ / L ≤ C₀' / L := div_le_div_of_nonneg_right hC hL.le
  have hrp : (A / 2) ^ (-η) ≤ (A / 2) ^ (-η') :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hX : (L : ℝ)⁻¹ + (A / 2) ^ (-η) ≤ (L : ℝ)⁻¹ + (A / 2) ^ (-η') := by linarith
  have hX0 : 0 ≤ (L : ℝ)⁻¹ + (A / 2) ^ (-η) :=
    add_nonneg (inv_nonneg.2 hL.le) (Real.rpow_nonneg (by linarith) _)
  refine ⟨a1, a2, a3, a4.trans (ENNReal.ofReal_le_ofReal ?_),
    a5.trans (ENNReal.ofReal_le_ofReal ?_), a6.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · have := mul_le_mul_of_nonneg_right hdiv hwl
    linarith
  · have := mul_le_mul_of_nonneg_right hdiv hdd
    linarith
  · have : 8 * C₀ * ((L : ℝ)⁻¹ + (A / 2) ^ (-η)) ≤ 8 * C₀' * ((L : ℝ)⁻¹ + (A / 2) ^ (-η')) :=
      mul_le_mul (by linarith) hX hX0 (by linarith)
    have := mul_le_mul_of_nonneg_right this hk
    linarith

/-! ### Constants -/

/-- The constant of `|ν' - L² μ|`. -/
def cNuL (R : RGPar 2 L N) (Λ cm : ℝ) : ℝ :=
  16 / 7 * (L : ℝ) ^ 2 * (8 * R.ℓ ^ 2 / 49 + 16 * R.ℓ ^ 2 / 147) * cmu Λ cm +
    3 * (L : ℝ) ^ 2 * cZ R + 8 * R.ℓ ^ 2 / 49 + (L : ℝ) ^ 2 * (16 * R.ℓ ^ 2 / 147)

/-- The constant of `‖D'‖`. -/
def cDL (R : RGPar 2 L N) (Λ κ cm cT C₂ CD : ℝ) : ℝ :=
  cx κ cT + CD * (cV R Λ cm ^ 2 + cW R Λ cm C₂ + 1) ^ 2

/-- The constant of `‖K'‖`. -/
def cKL (R : RGPar 2 L N) (Λ κ cm cT C₂ CK : ℝ) : ℝ :=
  cx κ cT + CK * (cR R Λ cm C₂ ^ 3 + 8 * cR R Λ cm C₂ * cx κ cT + 64 * cx κ cT ^ 2)

/-- The remainder bound of `apriori`, in the form used for both sets of constants. -/
theorem rem_bound {Cq Cl cS cxv cRv k v w ε g : ℝ} (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl)
    (hcS : 0 ≤ cS) (hcx : 0 ≤ cxv) (hg : 0 ≤ g) (hε : 0 ≤ ε)
    (hk : k ≤ cxv * (ε * g)) (hv0 : 0 ≤ v) (hv : v ≤ cRv * g) (hw : w ≤ (cRv * g) ^ 2)
    (hg2 : g ^ 2 ≤ ε * g) :
    2 * Cq * (cS * (Cl * (8 * k))) + Cq * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) ≤
      (16 * Cq * cS * Cl * cxv + Cq * Cl * (L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 + Q1 2) *
        cRv ^ 2) * (ε * g) := by
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have hN0 : 0 ≤ cNear 2 L := Nat.cast_nonneg _
  have hs : BH.sig 2 L v w ≤ (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cRv ^ 2 * (ε * g) := by
    unfold BH.sig
    have h1 : v ^ 2 ≤ (cRv * g) ^ 2 := pow_le_pow_left₀ hv0 hv 2
    have h2 : (cRv * g) ^ 2 ≤ cRv ^ 2 * (ε * g) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hg2 (sq_nonneg _)
    have a1 := mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hN0 (sq_nonneg (Q1 2)))
    have a2 := mul_le_mul_of_nonneg_left (hw.trans h2) (by linarith : (0 : ℝ) ≤ Q1 2)
    linarith only [a1, a2, show (cNear 2 L * Q1 2 ^ 2 + Q1 2) * cRv ^ 2 * (ε * g) =
      cNear 2 L * Q1 2 ^ 2 * (cRv ^ 2 * (ε * g)) + Q1 2 * (cRv ^ 2 * (ε * g)) by ring]
  have t1 : 2 * Cq * (cS * (Cl * (8 * k))) ≤ 16 * Cq * cS * Cl * cxv * (ε * g) := by
    have := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 16 * Cq * cS * Cl)
    linarith only [this, show 2 * Cq * (cS * (Cl * (8 * k))) = 16 * Cq * cS * Cl * k by ring,
      show 16 * Cq * cS * Cl * (cxv * (ε * g)) = 16 * Cq * cS * Cl * cxv * (ε * g) by ring]
  have t2 := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ Cq * Cl * (L : ℝ) ^ 2)
  linarith only [t1, t2, show Cq * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) =
    Cq * Cl * (L : ℝ) ^ 2 * BH.sig 2 L v w by ring]

theorem rem_bound_cE (R : RGPar 2 L N) [Fact (0 < R.ℓ)] {Λ κ cm cT C₂ Cq Cl cS k v w ε g : ℝ}
    (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl) (hcS : 0 ≤ cS) (hcx : 0 ≤ cx κ cT) (hg : 0 ≤ g) (hε : 0 ≤ ε)
    (hk : k ≤ cx κ cT * (ε * g)) (hv0 : 0 ≤ v) (hv : v ≤ cR R Λ cm C₂ * g)
    (hw : w ≤ (cR R Λ cm C₂ * g) ^ 2) (hg2 : g ^ 2 ≤ ε * g) :
    2 * Cq * (cS * (Cl * (8 * k))) + Cq * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) ≤
      cE R Λ κ cm cT C₂ Cq Cl cS * ε * R.ℓ ^ 2 * g := by
  have hℓ : 0 < R.ℓ := Fact.out
  have h := rem_bound (L := L) hCq hCl hcS hcx hg hε hk hv0 hv hw hg2
  refine h.trans (le_of_eq ?_)
  unfold cE
  field_simp

/-! ### Scalar algebra -/

theorem nu_alg {X Lsq ℓ2 g Cq RQ RL mu cmuv cZv : ℝ}
    (hX : X ≤ 16 / 7 * Lsq * (8 * ℓ2 / 49 * g + (2 * Cq * RQ + Cq * RL) / ℓ2) * mu +
      3 * Lsq * (cZv * g) + 8 * ℓ2 / 49 * g + 2 * (Lsq * Cq * RQ + Cq * RL) / ℓ2)
    (hE : (2 * Cq * RQ + Cq * RL) / ℓ2 ≤ 16 * ℓ2 / 147 * g) (hRQ : 0 ≤ Cq * RQ)
    (hRL : 0 ≤ Cq * RL) (hL : 2 ≤ Lsq) (hℓ : 0 < ℓ2) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hmu0 : 0 ≤ mu) (hmu : mu ≤ cmuv * g) :
    X ≤ (16 / 7 * Lsq * (8 * ℓ2 / 49 + 16 * ℓ2 / 147) * cmuv + 3 * Lsq * cZv + 8 * ℓ2 / 49 +
      Lsq * (16 * ℓ2 / 147)) * g := by
  have hE0 : 0 ≤ (2 * Cq * RQ + Cq * RL) / ℓ2 := by
    apply div_nonneg _ hℓ.le; linarith only [hRQ, hRL]
  have hA : 8 * ℓ2 / 49 * g + (2 * Cq * RQ + Cq * RL) / ℓ2 ≤ 8 * ℓ2 / 49 + 16 * ℓ2 / 147 := by
    have a1 : 8 * ℓ2 / 49 * g ≤ 8 * ℓ2 / 49 := by
      have := mul_le_mul_of_nonneg_left hg1 (by positivity : (0 : ℝ) ≤ 8 * ℓ2 / 49)
      linarith only [this]
    have a2 : 16 * ℓ2 / 147 * g ≤ 16 * ℓ2 / 147 := by
      have := mul_le_mul_of_nonneg_left hg1 (by positivity : (0 : ℝ) ≤ 16 * ℓ2 / 147)
      linarith only [this]
    linarith only [a1, a2, hE]
  have hA0 : 0 ≤ 8 * ℓ2 / 49 * g + (2 * Cq * RQ + Cq * RL) / ℓ2 := by
    have : 0 ≤ 8 * ℓ2 / 49 * g := by positivity
    linarith only [this, hE0]
  have e1 : (8 * ℓ2 / 49 * g + (2 * Cq * RQ + Cq * RL) / ℓ2) * mu ≤
      (8 * ℓ2 / 49 + 16 * ℓ2 / 147) * (cmuv * g) :=
    mul_le_mul hA hmu hmu0 (by positivity)
  have e2 := mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ 16 / 7 * Lsq)
  have e3 : 2 * (Lsq * Cq * RQ + Cq * RL) / ℓ2 ≤ Lsq * ((2 * Cq * RQ + Cq * RL) / ℓ2) := by
    rw [mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hℓ.le
    have := mul_le_mul_of_nonneg_right hL hRL
    linarith only [this, show Lsq * (2 * Cq * RQ + Cq * RL) = 2 * (Lsq * (Cq * RQ)) +
      Lsq * (Cq * RL) by ring, show 2 * (Lsq * Cq * RQ + Cq * RL) = 2 * (Lsq * (Cq * RQ)) +
      2 * (Cq * RL) by ring]
  have e4 := mul_le_mul_of_nonneg_left hE (by linarith only [hL] : (0 : ℝ) ≤ Lsq)
  have e5 : 16 / 7 * Lsq * (8 * ℓ2 / 49 * g + (2 * Cq * RQ + Cq * RL) / ℓ2) * mu =
      16 / 7 * Lsq * ((8 * ℓ2 / 49 * g + (2 * Cq * RQ + Cq * RL) / ℓ2) * mu) := by ring
  linarith only [hX, e2, e3, e4, e5]

theorem w_alg {X C₂ v cVv g a cWv : ℝ} (hX : X ≤ C₂ * v ^ 2 + a * (cWv * g ^ 2))
    (hC₂ : 0 ≤ C₂) (hv0 : 0 ≤ v) (hv : v ≤ cVv * g) (ha : a ≤ 1 / 4)
    (hcW : cWv = 3 * C₂ * cVv ^ 2 + 1) : X ≤ cWv * g ^ 2 := by
  subst hcW
  have h1 : v ^ 2 ≤ cVv ^ 2 * g ^ 2 := by rw [← mul_pow]; exact pow_le_pow_left₀ hv0 hv 2
  have h2 := mul_le_mul_of_nonneg_left h1 hC₂
  have hW0 : 0 ≤ (3 * C₂ * cVv ^ 2 + 1) * g ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_right ha hW0
  have h4 : 0 ≤ C₂ * cVv ^ 2 * g ^ 2 := by positivity
  linarith only [hX, h2, h3, h4, sq_nonneg g]

theorem z_alg {X ℓ2 g E : ℝ} (hX : X ≤ 8 * ℓ2 / 49 * g + E) (hE : E ≤ 16 * ℓ2 / 147 * g)
    (hℓ : 0 ≤ ℓ2) (hg : 0 ≤ g) : X ≤ 16 * ℓ2 / 49 * g := by
  have : 0 ≤ ℓ2 * g := mul_nonneg hℓ hg
  linarith only [hX, hE, this]

theorem g_alg {X g E : ℝ} (hX : X ≤ 2 * g + 2 * E) (hE : E ≤ g / 24) (hg : 0 ≤ g) :
    X ≤ 3 * g := by
  linarith only [hX, hE, hg]

theorem g_alg' {X g E : ℝ} (hX : g / 6 - 2 * E ≤ X) (hE : E ≤ g / 24) : g / 12 ≤ X := by
  linarith only [hX, hE]

theorem d_alg {X a dd CD v cVv cWv g cxv : ℝ}
    (hX : X ≤ a * dd + CD * (v ^ 2 + (cWv * g ^ 2 + dd)) ^ 2) (ha : a ≤ 1 / 4) (hdd0 : 0 ≤ dd)
    (hdd : dd ≤ cxv * g ^ 3) (hdd2 : dd ≤ g ^ 2) (hCD : 0 ≤ CD) (hv0 : 0 ≤ v)
    (hv : v ≤ cVv * g) (hcW : 0 ≤ cWv) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hcx : 0 ≤ cxv) :
    X ≤ (cxv + CD * (cVv ^ 2 + cWv + 1) ^ 2) * g ^ 2 := by
  have hg32 : g ^ 3 ≤ g ^ 2 := by
    have := mul_le_mul_of_nonneg_left hg1 (sq_nonneg g)
    linarith only [this, show g ^ 3 = g ^ 2 * g by ring]
  have hg42 : g ^ 4 ≤ g ^ 2 := by
    have h := pow_le_one₀ hg0 hg1 (n := 2)
    have := mul_le_mul_of_nonneg_left h (sq_nonneg g)
    linarith only [this, show g ^ 4 = g ^ 2 * g ^ 2 by ring]
  have a1 : a * dd ≤ cxv * g ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right ha hdd0
    have h2 := mul_le_mul_of_nonneg_left hg32 hcx
    linarith only [h1, h2, hdd, show 0 ≤ cxv * g ^ 3 by positivity]
  have h1 : v ^ 2 ≤ cVv ^ 2 * g ^ 2 := by rw [← mul_pow]; exact pow_le_pow_left₀ hv0 hv 2
  have hs : v ^ 2 + (cWv * g ^ 2 + dd) ≤ (cVv ^ 2 + cWv + 1) * g ^ 2 := by
    linarith only [h1, hdd2, show (cVv ^ 2 + cWv + 1) * g ^ 2 = cVv ^ 2 * g ^ 2 + cWv * g ^ 2 +
      g ^ 2 by ring]
  have hs0 : 0 ≤ v ^ 2 + (cWv * g ^ 2 + dd) := by positivity
  have hs2 := pow_le_pow_left₀ hs0 hs 2
  have h4 := mul_le_mul_of_nonneg_left hg42 (by positivity : (0 : ℝ) ≤ (cVv ^ 2 + cWv + 1) ^ 2)
  have a2 := mul_le_mul_of_nonneg_left (hs2.trans (le_of_eq (by ring) |>.trans h4)) hCD
  linarith only [hX, a1, a2, show (cxv + CD * (cVv ^ 2 + cWv + 1) ^ 2) * g ^ 2 =
    cxv * g ^ 2 + CD * ((cVv ^ 2 + cWv + 1) ^ 2 * g ^ 2) by ring]

/-! ### One step under `ValidAtL` -/

set_option maxHeartbeats 4000000 in
/-- **The output of one step under `ValidAtL`**, for inputs with the a priori bounds. -/
theorem glue_core {C₀ η εs CK C₂ CD Cq Cl cS Cqg Clg cSg : ℝ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hSB : Last.StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS) (hGB : GStepBound L R.A Cqg Clg cSg)
    {j : ℕ} (hVL : ValidAtL R j) {st : RawSt 2 L N} (HI : RawInv R j st)
    (hm : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    {Λ κ cg cm cT ε : ℝ} (H : ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    (hκ₁ : kap1 L R.A C₀ η ≤ 1) (hCK : 0 ≤ CK) (hCD : 0 ≤ CD)
    (hCqg : 0 ≤ Cqg) (hClg : 0 ≤ Clg) (hcSg : 1 ≤ cSg)
    (hcE : cE R Λ κ cm cT C₂ Cqg Clg cSg * ε ≤ R.ℓ ^ 2 / 24) (hr1 : cR R Λ cm C₂ * ε ≤ 1)
    (hk1 : 8 * cx κ cT * ε ≤ 1)
    {g μ : ℝ} (x : Xs R j) (hg : 0 < g) (hgε : g ≤ ε) (hμ : |μ| ≤ cmu Λ cm * g)
    (hx : ‖x‖ ≤ cx κ cT * g ^ 3)
    (hz : ‖st.z / st.Z‖ ≤ cZ R * g) (hy : ‖st.y / st.Z‖ ≤ cZ R * g)
    (hWl : Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal (cW R Λ cm C₂ * g ^ 2)) :
    ‖(rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).st.z /
        (rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).st.Z‖ ≤ cZ R * g ∧
    ‖(rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).st.y /
        (rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).st.Z‖ ≤ cZ R * g ∧
    ‖(rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).nu - (L : ℂ) ^ 2 * (μ : ℂ)‖ ≤
      cNuL R Λ cm * g ∧
    Fnorm (j + 1) (fscale (rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).st.Z * R.ℓ)
      (rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).st.Wl ≤
      ENNReal.ofReal (cW R Λ cm C₂ * g ^ 2) ∧
    Fnorm (j + 1) (fscale (rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).st.Z * R.ℓ)
      (rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).D ≤
      ENNReal.ofReal (cDL R Λ κ cm cT C₂ CD * g ^ 2) ∧
    Knorm (j + 1) (fscale (rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).st.Z * R.ℓ) R.A
      (rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).K ≤
      ENNReal.ofReal (cKL R Λ κ cm cT C₂ CK * g ^ 3) ∧
    ‖(rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).g‖ ≤ 3 * g ∧
    g / 12 ≤ (rawStep R j st g μ (rawD R st.u x) (rawK R st.u x)).g.re := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hρ1 : R.ρ < 1 := by linarith [hVL.2.2.2.2.2.1]
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  have hε0 : 0 ≤ ε := H.hε.le
  -- the radius
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hcr : 0 ≤ cR R Λ cm C₂ := by unfold cR; positivity
  have hcx := H.hcx
  have hg1 : g ≤ 1 := hgε.trans H.hε1
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
  have hg2 : g ^ 2 ≤ ε * g := by nlinarith
  have hg3 : g ^ 3 ≤ ε * g ^ 2 := by
    rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
  have hg3' : g ^ 3 ≤ ε * g := by nlinarith [pow_le_one₀ hg.le hg1 (n := 2)]
  have hg32 : g ^ 3 ≤ g ^ 2 := pow_le_pow_of_le_one hg.le hg1 (by norm_num)
  have hdd : ‖x.1‖ ≤ g ^ 2 := by
    have := H.h3; nlinarith [mul_le_mul_of_nonneg_left hg3 H.hcx, sq_nonneg g]
  have hv : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ cV R Λ cm * g := by
    unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu Λ cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤
      cR R Λ cm C₂ * g := by
    refine hv.trans ?_; unfold cR; nlinarith
  have hwr : cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ (cR R Λ cm C₂ * g) ^ 2 := by
    unfold cR
    have h1 : cW R Λ cm C₂ + 1 ≤ (cV R Λ cm + cW R Λ cm C₂ + 2) ^ 2 := by nlinarith
    nlinarith [sq_nonneg g]
  have hrε : cR R Λ cm C₂ * g ≤ εs :=
    (mul_le_mul_of_nonneg_left hgε hcr).trans H.h4
  have hr1' : cR R Λ cm C₂ * g ≤ 1 := (mul_le_mul_of_nonneg_left hgε hcr).trans hr1
  have hk3 : cx κ cT * g ^ 3 ≤ cx κ cT * ε := by
    have : g ^ 3 ≤ ε := by nlinarith [sq_nonneg g, pow_le_one₀ hg.le hg1 (n := 2)]
    exact mul_le_mul_of_nonneg_left this H.hcx
  have hkε : 8 * ‖x.2‖ ≤ εs := by linarith [H.h5]
  have hk8 : 8 * ‖x.2‖ ≤ 1 := by linarith
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hv0 : 0 ≤ cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g := by
    have hM : 0 ≤ cM := Nat.cast_nonneg _; positivity
  have hk : ‖x.2‖ ≤ cx κ cT * (ε * g) := hx2.trans (mul_le_mul_of_nonneg_left hg3' H.hcx)
  -- the step bounds
  obtain ⟨c1, c2, c3, cw, cD, cK⟩ := hSB N R j hVL st HI g μ (rawD R st.u x) (rawK R st.u x)
    (rawD_mem R _ _) (rawK_mem R _ _) hm hg.le (cZ R * g) hz hy hη hηs
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ (cR R Λ cm C₂ * g) (by positivity) (norm_nonneg _)
    (norm_nonneg _) hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x)) (le_of_eq (Knorm_rawK R HI.hu hZ x))
    hvr hwr hrε hkε
  obtain ⟨g1, g2⟩ := hGB N R j hVL st HI g μ (rawD R st.u x) (rawK R st.u x)
    (rawD_mem R _ _) (rawK_mem R _ _) hm hg.le (cZ R * g) hz hy hη hηs
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ (cR R Λ cm C₂ * g) (by positivity) (norm_nonneg _)
    (norm_nonneg _) hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x)) (le_of_eq (Knorm_rawK R HI.hu hZ x))
    hvr hwr hr1' hk8
  -- the remainders
  have hE := rem_bound_cE R H.hCq H.hCl (le_trans zero_le_one H.hcS) H.hcx hg.le hε0 hk hv0 hvr hwr hg2
  have hE' : cE R Λ κ cm cT C₂ Cq Cl cS * ε * R.ℓ ^ 2 * g ≤ 16 * R.ℓ ^ 2 / 147 * R.ℓ ^ 2 * g := by
    have := mul_le_mul_of_nonneg_right H.h7 (by positivity : (0 : ℝ) ≤ R.ℓ ^ 2 * g)
    linarith only [this]
  have hEd : (2 * Cq * (cS * (Cl * (8 * ‖x.2‖))) + Cq * (Cl * ((L : ℝ) ^ 2 *
      BH.sig 2 L (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g)
        (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖)))) / R.ℓ ^ 2 ≤ 16 * R.ℓ ^ 2 / 147 * g := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [hE, hE', show 16 * R.ℓ ^ 2 / 147 * g * R.ℓ ^ 2 =
      16 * R.ℓ ^ 2 / 147 * R.ℓ ^ 2 * g by ring]
  have hEg := rem_bound_cE R hCqg hClg (le_trans zero_le_one hcSg) H.hcx hg.le hε0 hk hv0 hvr hwr hg2
    (Cq := Cqg) (Cl := Clg) (cS := cSg)
  have hgE : gErr L Cqg Clg cSg R.ℓ ‖x.2‖ (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) +
      8 * R.ℓ ^ 4 * g) (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖) ≤ g / 24 := by
    unfold gErr
    rw [div_div, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hcE (by positivity : (0 : ℝ) ≤ R.ℓ ^ 2 * g)
    linarith only [hEg, this, show g / 24 * (R.ℓ ^ 2 * R.ℓ ^ 2) = R.ℓ ^ 2 / 24 * (R.ℓ ^ 2 * g)
      by ring, show cE R Λ κ cm cT C₂ Cqg Clg cSg * ε * R.ℓ ^ 2 * g =
      cE R Λ κ cm cT C₂ Cqg Clg cSg * ε * (R.ℓ ^ 2 * g) by ring]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `z`
    exact z_alg c1 hEd (sq_nonneg _) hg.le
  · exact z_alg c2 hEd (sq_nonneg _) hg.le
  · -- `ν`
    have hL2 : (2 : ℝ) ≤ (L : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := hVL.1; omega)
      exact this.trans (le_self_pow₀ (by linarith only [this]) (by norm_num))
    have hRQ0 : 0 ≤ Cq * (cS * (Cl * (8 * ‖x.2‖))) := by
      have := H.hCq; have := H.hCl; have : (0 : ℝ) ≤ cS := le_trans zero_le_one H.hcS
      positivity
    have hRL0 : 0 ≤ Cq * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L
        (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g)
          (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖))) := by
      have := BH.sig_nonneg (L := L) (d := 2) (by norm_num)
        (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g)
        (cW R Λ cm C₂ * g ^ 2 + ‖x.1‖) (by positivity)
      have := H.hCq; have := H.hCl
      positivity
    exact nu_alg c3 hEd hRQ0 hRL0 hL2 (by positivity) hg.le hg1 (abs_nonneg μ) hμ
  · -- `W^lin`
    exact cw.trans (ENNReal.ofReal_le_ofReal (w_alg (le_refl _) H.hC₂ hv0 hv H.hC₀ rfl))
  · -- `D`
    refine cD.trans (ENNReal.ofReal_le_ofReal ?_)
    unfold cDL
    exact d_alg (le_refl _) H.hC₀ (norm_nonneg _) hx1 hdd hCD hv0 hv hcw hg.le hg1 H.hcx
  · -- `K`
    refine cK.trans (ENNReal.ofReal_le_ofReal ?_)
    have e : kap1 L R.A C₀ η = 8 * C₀ * ((L : ℝ)⁻¹ + (R.A / 2) ^ (-η)) := rfl
    rw [← e]
    have k0 := norm_nonneg x.2
    have hg43 : g ^ 4 ≤ g ^ 3 := pow_le_pow_of_le_one hg.le hg1 (by norm_num)
    have hg63 : g ^ 6 ≤ g ^ 3 := pow_le_pow_of_le_one hg.le hg1 (by norm_num)
    have b1 : kap1 L R.A C₀ η * ‖x.2‖ ≤ cx κ cT * g ^ 3 :=
      (mul_le_mul_of_nonneg_right hκ₁ k0).trans (by linarith only [hx2])
    have b3 : cR R Λ cm C₂ * g * (8 * ‖x.2‖) ≤ 8 * cR R Λ cm C₂ * cx κ cT * g ^ 3 := by
      have h1 := mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ 8 * cR R Λ cm C₂ * g)
      have h2 := mul_le_mul_of_nonneg_left hg43 (by positivity : (0 : ℝ) ≤ 8 * cR R Λ cm C₂ * cx κ cT)
      linarith only [h1, h2, show 8 * cR R Λ cm C₂ * g * (cx κ cT * g ^ 3) =
        8 * cR R Λ cm C₂ * cx κ cT * g ^ 4 by ring,
        show cR R Λ cm C₂ * g * (8 * ‖x.2‖) = 8 * cR R Λ cm C₂ * g * ‖x.2‖ by ring]
    have b4 : (8 * ‖x.2‖) ^ 2 ≤ 64 * cx κ cT ^ 2 * g ^ 3 := by
      have h1 := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hx2
        (by norm_num : (0 : ℝ) ≤ 8)) 2
      have h2 := mul_le_mul_of_nonneg_left hg63 (by positivity : (0 : ℝ) ≤ 64 * cx κ cT ^ 2)
      linarith only [h1, h2, show (8 * (cx κ cT * g ^ 3)) ^ 2 = 64 * cx κ cT ^ 2 * g ^ 6 by ring]
    have b5 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (le_of_eq
      (show (cR R Λ cm C₂ * g) ^ 3 = cR R Λ cm C₂ ^ 3 * g ^ 3 by ring)) b3) b4) hCK
    unfold cKL
    linarith only [b1, b5]
  · -- `|ǧ'|`
    exact g_alg g1 hgE hg.le
  · exact g_alg' g2 hgE

/-! ### Along a regular history -/

set_option maxHeartbeats 4000000 in
/-- **The step `j = N_h` along a regular history** (with `ValidAtL` at `N_h`). -/
theorem glue_step {C₀ η εs CK C₂ CD Cq Cl cS Cqg Clg cSg : ℝ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hSB : Last.StepBounds L R.A C₀ η εs CK C₂ CD Cq Cl cS) (hGB : GStepBound L R.A Cqg Clg cSg)
    {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j ≤ Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    {Λ β δ κ cg cm cT ε : ℝ} (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq Cl cS)
    (hκ₁ : kap1 L R.A C₀ η ≤ 1) (hCK : 0 ≤ CK) (hCD : 0 ≤ CD)
    (hCqg : 0 ≤ Cqg) (hClg : 0 ≤ Clg) (hcSg : 1 ≤ cSg)
    (hcE : cE R Λ κ cm cT C₂ Cqg Clg cSg * ε ≤ R.ℓ ^ 2 / 24) (hr1 : cR R Λ cm C₂ * ε ≤ 1)
    (hk1 : 8 * cx κ cT * ε ≤ 1)
    (t : Hist.Seq (Xs R)) (ht : Hist.InDh Λ β δ κ cg cm cT ε Nh t) :
    ‖(histOut R Nh t).st.z / (histOut R Nh t).st.Z‖ ≤ cZ R * (t Nh).1 ∧
    ‖(histOut R Nh t).st.y / (histOut R Nh t).st.Z‖ ≤ cZ R * (t Nh).1 ∧
    ‖(histOut R Nh t).nu - (L : ℂ) ^ 2 * ((t Nh).2.1 : ℂ)‖ ≤ cNuL R Λ cm * (t Nh).1 ∧
    Fnorm (Nh + 1) (fscale (histOut R Nh t).st.Z * R.ℓ) (histOut R Nh t).st.Wl ≤
      ENNReal.ofReal (cW R Λ cm C₂ * (t Nh).1 ^ 2) ∧
    Fnorm (Nh + 1) (fscale (histOut R Nh t).st.Z * R.ℓ) (histOut R Nh t).D ≤
      ENNReal.ofReal (cDL R Λ κ cm cT C₂ CD * (t Nh).1 ^ 2) ∧
    Knorm (Nh + 1) (fscale (histOut R Nh t).st.Z * R.ℓ) R.A (histOut R Nh t).K ≤
      ENNReal.ofReal (cKL R Λ κ cm cT C₂ CK * (t Nh).1 ^ 3) ∧
    ‖(histOut R Nh t).g‖ ≤ 3 * (t Nh).1 ∧ (t Nh).1 / 12 ≤ (histOut R Nh t).g.re := by
  have hSB' := hSB.toStepBounds hVL.1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB' hV (fun j hj => hm j hj.le) hβ hδ1 H Nh le_rfl t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 Nh le_rfl
  have HI := rawInv_hist R hVL.2.2.2.2.1 Nh hV t
  exact glue_core R hSB hGB hVL HI (hm Nh le_rfl) H hκ₁ hCK hCD hCqg hClg hcSg hcE hr1 hk1
    (t Nh).2.2 hg hgε hμ hx hz hy hWl

theorem traj_succ_rg (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Λ b μ₀ : ℝ) (j : ℕ) :
    Hist.traj (rgData R) Λ b μ₀ (j + 1) =
      Hist.stepS (rgData R) Λ j (Hist.traj (rgData R) Λ b μ₀) :=
  Hist.tr_succ _ _ (fun t t' h => by
    simp only [Hist.stepS, causal_G R j t t' h, causal_m R j t t' h, causal_T R j t t' h,
      h j le_rfl])

/-- Admissible trajectories of `rgData` are regular (from (F1)). -/
theorem admissible_InDh_rg (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ}
    {Λ β δ κ cg cm cT ε : ℝ}
    (F1 : ∀ j < Nh, ∀ t, Hist.InDh Λ β δ κ cg cm cT ε j t →
      |(rgData R).G j t - (t j).1 - β * (t j).1 ^ 2| ≤ δ * β * (t j).1 ^ 2 + cg * (t j).1 ^ 3)
    {b μ₀ : ℝ} (h : Hist.Admissible (rgData R) Λ κ cm cT Nh ε b μ₀) :
    ∀ j ≤ Nh, Hist.InDh Λ β δ κ cg cm cT ε j (Hist.traj (rgData R) Λ b μ₀) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨fun i hi => h.1 i (by omega), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ j ih =>
    intro hj
    have hs := ih (by omega)
    refine ⟨fun i hi => h.1 i (by omega), fun i hi => ?_⟩
    rcases (show i = j ∨ i < j by omega) with rfl | hij
    · rw [traj_succ_rg R Λ b μ₀ i]; exact F1 i (by omega) _ hs
    · exact hs.2 i hij

end

end Step2
