import Ward.Model
import Ward.IVT

/-!
# Corollary `cor:ward`

For the model identification `(b, m²) ↦ (β, h) = (betaF, hF)` of `Ward.Model`:

**(i)** (`cor_ward_i`) for real `0 < b ≤ b̄` and `m² ≥ 0`:
`|h(b, m²) - m² β(b, m²)| ≤ C b m² β(b, m²)`; in particular `h(b, 0) = 0` and `h(b, m²) > 0` for
`m² > 0`.

Proof: for `m² > 0` and every `N` with `m² L^{2N} ≥ 1`, the Ward identity `⟨z_0⟩ = h ∑_x ⟨ξ_0η_x⟩`
(`H02.ward`) and the bridge give `1 - c²⟨ψ̄_0ψ_0⟩_N = h c² ∑_x ⟨ψ̄_0ψ_x⟩_N` with
`∑_x ⟨ψ̄_0ψ_x⟩_N = 1/m² + O(b L^{-(2+κ)N})/m⁴` (`e:psi4-suscept`) and `⟨ψ̄_0ψ_0⟩_N = O(1)`
(`e:psi4-00` and `|W_N(0)| ≤ 2ℓ₀²`); letting `N → ∞` gives the bound (`ward_core`). The case
`m² = 0` follows by continuity in `m²`.

**(ii)** (`cor_ward_ii`) there is `β₀` such that for `β ≥ β₀`, `h ≥ 0` there are `b̃(β,h) ∈ (0, b̄]`,
`m̃²(β,h) ≥ 0` (`> 0` for `h > 0`) with `β(b̃, m̃²) = β`, `h(b̃, m̃²) = h`, `m̃²(β, 0) = 0`,
`m̃² → 0` and `b̃ → b̃(β, 0)` as `h ↓ 0`, and `b̃(β,0)` is the unique `b ∈ (0, b̄]` with
`β(b, 0) = β`. Proof by monotonicity and the intermediate value theorem (`ivt_solution`), which
replaces the reference to MR3339164 in the paper.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Filter Topology

/-! ### The algebra of the Ward identity -/

theorem ward_alg {h m β c2 s b C K₁ : ℝ} {g E : ℂ} (hm : 0 < m) (hb : 0 < b)
    (hs1 : |s| ≤ 2 * C * b) (hs2 : 2 * C * b ≤ 1 / 2) (hβ : β = (1 + s) ^ 2 / b)
    (hc : c2 = b / (1 + s)) (hg : ‖g‖ ≤ K₁)
    (heq : (1 : ℂ) - c2 * g = h * (c2 * (1 / m + E / m ^ 2))) :
    |h - m * β| ≤ (4 * C + 4 * K₁) * b * (m * β) + |h| * ‖E‖ / m := by
  have hsl : -(1 / 2) ≤ s := by have := (abs_le.1 hs1).1; linarith
  have hs0 : 0 < 1 + s := by linarith
  have hc0 : c2 ≠ 0 := by rw [hc]; positivity
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hc0' : (c2 : ℂ) ≠ 0 := by exact_mod_cast hc0
  have e1 : (h : ℂ) * (1 + E / m) = m / c2 - m * g := by
    calc (h : ℂ) * (1 + E / m) = (m / c2) * (h * (c2 * (1 / m + E / m ^ 2))) := by
          field_simp
      _ = (m / c2) * (1 - c2 * g) := by rw [heq]
      _ = m / c2 - m * g := by field_simp
  have e2 : ((h - m * β : ℝ) : ℂ) = ((m / c2 - m * β : ℝ) : ℂ) - m * g - h * E / m := by
    push_cast; linear_combination e1
  have e3 : m / c2 - m * β = -(m * β) * (s / (1 + s)) := by
    rw [hc, hβ]; field_simp; ring
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans hg
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hβb : 1 ≤ 4 * b * β := by
    rw [hβ, show 4 * b * ((1 + s) ^ 2 / b) = 4 * (1 + s) ^ 2 by field_simp]
    nlinarith
  have hq : |s / (1 + s)| ≤ 4 * C * b := by
    rw [abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
    have h4 : 0 ≤ 4 * C * b := by
      have := abs_nonneg s; linarith
    nlinarith
  have hmβ : 0 ≤ m * β := mul_nonneg hm.le hβ0
  calc |h - m * β| = ‖((h - m * β : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖((m / c2 - m * β : ℝ) : ℂ) - m * g - h * E / m‖ := by rw [e2]
    _ ≤ ‖((m / c2 - m * β : ℝ) : ℂ)‖ + ‖(m : ℂ) * g‖ + ‖(h : ℂ) * E / m‖ := by
        linarith [norm_sub_le (((m / c2 - m * β : ℝ) : ℂ)) ((m : ℂ) * g),
          norm_sub_le (((m / c2 - m * β : ℝ) : ℂ) - (m : ℂ) * g) ((h : ℂ) * E / m)]
    _ = |m / c2 - m * β| + m * ‖g‖ + |h| * ‖E‖ / m := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_div, norm_mul, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hm]
    _ ≤ 4 * C * b * (m * β) + 4 * K₁ * b * (m * β) + |h| * ‖E‖ / m := by
        have i1 : |m / c2 - m * β| ≤ 4 * C * b * (m * β) := by
          rw [e3, abs_mul, abs_neg, abs_of_nonneg hmβ, mul_comm]
          exact mul_le_mul_of_nonneg_right hq hmβ
        have i2 : m * ‖g‖ ≤ 4 * K₁ * b * (m * β) :=
          calc m * ‖g‖ ≤ m * K₁ := mul_le_mul_of_nonneg_left hg hm.le
            _ ≤ m * K₁ * (4 * b * β) := le_mul_of_one_le_right (mul_nonneg hm.le hK₁) hβb
            _ = 4 * K₁ * b * (m * β) := by ring
        linarith
    _ = (4 * C + 4 * K₁) * b * (m * β) + |h| * ‖E‖ / m := by ring

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

theorem exists_ne_zero_lam (hd : 1 ≤ d) (hL : 2 ≤ L) {N : ℕ} (hN : 1 ≤ N) :
    ∃ x : Lam d L N, x ≠ 0 := by
  have h2 : (2 : ℝ) ≤ ((L ^ N : ℕ) : ℝ) := by
    have : 2 ≤ L ^ N := le_trans hL (Nat.le_self_pow (by omega) L)
    exact_mod_cast this
  have h1 : (1 : ℝ) < Fintype.card (Lam d L N) := by
    rw [Suscept.card_lam]
    calc (1 : ℝ) < 2 := by norm_num
      _ ≤ ((L ^ N : ℕ) : ℝ) := h2
      _ = ((L ^ N : ℕ) : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ ((L ^ N : ℕ) : ℝ) ^ d := pow_le_pow_right₀ (by linarith) hd
  exact Fintype.exists_ne_of_one_lt_card (by exact_mod_cast h1) 0

/-- The constant of `cor:ward` (i): `4C + 4(2ℓ₀² + 3C_t)`. -/
def Kw (C ℓ₀ Ct : ℝ) : ℝ := 4 * C + 4 * (2 * ℓ₀ ^ 2 + 3 * Ct)

/-- **The core of `cor:ward` (i)**, `m² > 0`. -/
theorem ward_core (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) {bb Ct : ℝ}
    (hbb : bb ≤ lbar) (hCt : 0 ≤ Ct) (HB : Psi4Body d L V₀c lbar bb Ct κ) {b m : ℝ} (hb : 0 < b)
    (hbb' : b ≤ bb) (hs2 : 2 * C * b ≤ 1 / 2) (hb1 : b ≤ 1) (hm : 0 < m) :
    |hF V₀c b m - m * betaF V₀c b m| ≤ Kw C ℓ₀ Ct * b * (m * betaF V₀c b m) := by
  have HF := HW.toFlowData
  have hd1 : 1 ≤ d := by omega
  have hL2 := HF.hL2
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hs1 := abs_s0R_le HF hb.le (hbb'.trans hbb) hm.le
  have hsl : -(1 / 2) ≤ s0R V₀c b m := by have := (abs_le.1 hs1).1; linarith
  have hs : -1 < s0R V₀c b m := by linarith
  have hbnorm : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb.le]
  obtain ⟨-, -, -, -, hmain⟩ := HB
  set X := Kw C ℓ₀ Ct * b * (m * betaF V₀c b m) with hX
  set q : ℝ := (L : ℝ) ^ (-(2 + κ)) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith [HF.κ_pos])
  -- the bound at each large `N`
  have hev : ∀ᶠ N : ℕ in atTop, |hF V₀c b m - m * betaF V₀c b m| ≤
      X + |hF V₀c b m| * (Ct * b * q ^ N) / m := by
    have hpow : Tendsto (fun N : ℕ => ((L : ℝ) ^ 2) ^ N) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by nlinarith)
    filter_upwards [eventually_ge_atTop 1, hpow.eventually_ge_atTop (1 / m)] with N hN hLN
    have hmL : 1 ≤ m * (L : ℝ) ^ (2 * N) := by
      rw [pow_mul]
      have := mul_le_mul_of_nonneg_left hLN hm.le
      rwa [mul_one_div_cancel hm.ne'] at this
    obtain ⟨-, -, hu, ⟨E, hE, hS⟩, hx⟩ := hmain N m b hN hm hmL (by rw [hbnorm]; exact hbb')
    obtain ⟨x, hx0⟩ := exists_ne_zero_lam hd1 hL2 hN
    obtain ⟨⟨-, -, hga, -⟩, ⟨E', hE', hg⟩, -, -⟩ := hx x hx0
    have hgood := HF.good N m hm.le
    have hZ : ZM d L N V₀c m b ≠ 0 := by
      rw [ZM_eq (HF.hb m b), Suscept.EC_Z0 hd1 HF.hL8 hN hm hgood]
      exact mul_ne_zero (Complex.exp_ne_zero _) hu
    -- the Ward identity
    have hw := H02.ward (nnW d L N (betaF V₀c b m)) (nnW_symm _) (hF V₀c b m) (0 : Lam d L N)
    have hw' := congrArg (fun r : ℝ => (r : ℂ)) (hw.1.trans (hw.2.1.trans hw.2.2))
    simp only [Complex.ofReal_mul, Complex.ofReal_sum] at hw'
    rw [avg_z_eq HW.conj hb hs hm hZ] at hw'
    rw [Finset.sum_congr rfl fun y _ => avg_ξη_eq HW.conj hb hs hm (0 : Lam d L N) y,
      ← Finset.mul_sum, hS] at hw'
    -- the bound on `⟨ψ̄_0ψ_0⟩`
    have hW : ‖(WN (d := d) (n := L ^ N) stdPt m (L : ℝ) N (0 : Lam d L N) : ℂ)‖ ≤ 2 * ℓ₀ ^ 2 := by
      have h := norm_sum_covAt_le hd hL2 HF.hℓ₀ hgood (0 : Lam d L N) 0
      rwa [sum_covAt_ofReal, sum_covAt_eq_WN hm hN, sub_zero] at h
    have hr1 : (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) ≤ 1 :=
      rpow_neg_mul_le_one hL1.le (by have h3 : (3 : ℝ) ≤ d := (by exact_mod_cast hd); linarith) N
    have hr2 : (L : ℝ) ^ (-(κ * N)) ≤ 1 := rpow_neg_mul_le_one hL1.le HF.κ_pos.le N
    have hgb : ‖avgM d L N V₀c m b (psibar (0 : Lam d L N) * psi (0 : Lam d L N))‖ ≤
        2 * ℓ₀ ^ 2 + 3 * Ct := by
      rw [hg]
      rw [hbnorm] at hga hE'
      have e1 : ‖gamA2 d L N m (V₀c m b) lbar x‖ ≤ Ct * b + 2 * ℓ₀ ^ 2 := by
        have := norm_sub_norm_le (gamA2 d L N m (V₀c m b) lbar x)
          (WN (d := d) (n := L ^ N) stdPt m (L : ℝ) N (0 : Lam d L N) : ℂ)
        linarith
      have e2 : ‖E'‖ ≤ 2 * Ct := by
        refine hE'.trans ?_
        have : (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) + b * (L : ℝ) ^ (-(κ * N)) ≤ 2 := by
          have := mul_le_mul hb1 hr2 (by positivity) zero_le_one
          linarith
        nlinarith
      have e3 : Ct * b ≤ Ct := mul_le_of_le_one_right hCt hb1
      calc ‖gamA2 d L N m (V₀c m b) lbar x + E'‖ ≤ ‖gamA2 d L N m (V₀c m b) lbar x‖ + ‖E'‖ :=
            norm_add_le _ _
        _ ≤ 2 * ℓ₀ ^ 2 + 3 * Ct := by linarith
    have halg := ward_alg (h := hF V₀c b m) (β := betaF V₀c b m) (c2 := c2F V₀c b m) (C := C)
      (K₁ := 2 * ℓ₀ ^ 2 + 3 * Ct) hm hb hs1 hs2 rfl rfl hgb hw'
    refine halg.trans ?_
    have hEq : ‖E‖ ≤ Ct * b * q ^ N := by
      rw [hbnorm, rpow_neg_mul_nat (by positivity)] at hE
      exact hE
    rw [hX, Kw]
    gcongr
  -- the limit `N → ∞`
  have hlim : Tendsto (fun N : ℕ => X + |hF V₀c b m| * (Ct * b * q ^ N) / m) atTop
      (𝓝 (X + |hF V₀c b m| * (Ct * b * 0) / m)) :=
    tendsto_const_nhds.add ((((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul
      (Ct * b)).const_mul |hF V₀c b m|).div_const m)
  simp only [mul_zero, zero_div, add_zero] at hlim
  exact ge_of_tendsto hlim hev

/-! ### `cor:ward` (i) -/

/-- The joint continuity of `β(b, m²)`, `h(b, m²)` on `(0, λ̄) × [0, ∞)`. -/
theorem betaF_hF_cont (HF : FlowData d L A ℓ₀ V₀c lbar C κ) :
    ContinuousOn (fun p : ℝ × ℝ => betaF V₀c p.1 p.2) (Set.Ioo 0 lbar ×ˢ Set.Ici 0) ∧
    ContinuousOn (fun p : ℝ × ℝ => hF V₀c p.1 p.2) (Set.Ioo 0 lbar ×ˢ Set.Ici 0) := by
  obtain ⟨hs, ha⟩ := s0R_a0R_cont HF
  have hsub : Set.Ioo 0 lbar ×ˢ Set.Ici (0 : ℝ) ⊆ Set.Ico 0 lbar ×ˢ Set.Ici 0 :=
    Set.prod_mono Set.Ioo_subset_Ico_self subset_rfl
  have hs' := hs.mono hsub
  have ha' := ha.mono hsub
  have hne : ∀ p ∈ Set.Ioo 0 lbar ×ˢ Set.Ici (0 : ℝ), p.1 ≠ 0 := fun p hp => hp.1.1.ne'
  refine ⟨?_, ?_⟩
  · exact ((continuousOn_const.add hs').pow 2).div continuous_fst.continuousOn hne
  · exact continuousOn_const.add (((ha'.add continuous_snd.continuousOn).mul
      (continuousOn_const.add hs')).div continuous_fst.continuousOn hne)

/-- **`cor:ward` (i)** for a given `V₀c` with `FlowDataW`. -/
theorem cor_ward_i (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) :
    ∃ bbar K : ℝ, 0 < bbar ∧ bbar ≤ lbar / 2 ∧ bbar ≤ 1 ∧ 0 ≤ K ∧ K * bbar ≤ 1 / 2 ∧
      48 * C * bbar ≤ 1 ∧
      (∀ b m, 0 < b → b ≤ bbar → 0 ≤ m →
        |hF V₀c b m - m * betaF V₀c b m| ≤ K * b * (m * betaF V₀c b m)) ∧
      (∀ b, 0 < b → b ≤ bbar → hF V₀c b 0 = 0) ∧
      (∀ b m, 0 < b → b ≤ bbar → 0 < m → 0 < hF V₀c b m) := by
  have HF := HW.toFlowData
  have hC := HF.C_nonneg
  have hlbar := HF.lbar_pos
  obtain ⟨bb, Ct, hbb0, hbbl, hCt, HB⟩ := thm_psi4_of hd HF
  set K := Kw C ℓ₀ Ct with hK
  have hK0 : 0 ≤ K := by rw [hK, Kw]; positivity
  set bbar := min bb (min (lbar / 2) (min 1 (min (1 / (48 * C + 48)) (1 / (2 * K + 2)))))
    with hbbar
  have hb1 : bbar ≤ bb := min_le_left _ _
  have hb2 : bbar ≤ lbar / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hb3 : bbar ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb4 : bbar ≤ 1 / (48 * C + 48) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hb5 : bbar ≤ 1 / (2 * K + 2) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hbpos : 0 < bbar := lt_min hbb0 (lt_min (by linarith) (lt_min one_pos
    (lt_min (by positivity) (by positivity))))
  have h48 : 48 * C * bbar ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hb4 (by positivity : (0 : ℝ) ≤ 48 * C + 48)
    rw [mul_one_div_cancel (by positivity)] at this
    nlinarith
  have hKb : K * bbar ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hb5 (by positivity : (0 : ℝ) ≤ 2 * K + 2)
    rw [mul_one_div_cancel (by positivity)] at this
    nlinarith
  have hCb : ∀ b, b ≤ bbar → 2 * C * b ≤ 1 / 2 := fun b hb => by
    nlinarith [mul_le_mul_of_nonneg_left hb hC]
  -- the bound for `m² > 0`
  have hpos : ∀ b m, 0 < b → b ≤ bbar → 0 < m →
      |hF V₀c b m - m * betaF V₀c b m| ≤ K * b * (m * betaF V₀c b m) := by
    intro b m hb hbb hm
    exact ward_core hd HW hbbl hCt HB hb (hbb.trans hb1) (hCb b hbb) (hbb.trans hb3) hm
  -- extension to `m² = 0`
  have hall : ∀ b m, 0 < b → b ≤ bbar → 0 ≤ m →
      |hF V₀c b m - m * betaF V₀c b m| ≤ K * b * (m * betaF V₀c b m) := by
    intro b m hb hbb hm
    rcases hm.lt_or_eq with hm | rfl
    · exact hpos b m hb hbb hm
    obtain ⟨hβc, hhc⟩ := betaF_hF_cont HF
    have hbl : b ∈ Set.Ioo 0 lbar := ⟨hb, by linarith⟩
    have hmap : Set.MapsTo (fun m : ℝ => (b, m)) (Set.Ici 0) (Set.Ioo 0 lbar ×ˢ Set.Ici 0) :=
      fun m hm => ⟨hbl, hm⟩
    have hc1 : ContinuousOn (fun m : ℝ => (b, m)) (Set.Ici 0) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hβm := hβc.comp hc1 hmap
    have hhm := hhc.comp hc1 hmap
    have hf : ContinuousOn (fun m => K * b * (m * betaF V₀c b m) -
        |hF V₀c b m - m * betaF V₀c b m|) (Set.Ici 0) :=
      (continuousOn_const.mul (continuousOn_id.mul hβm)).sub
        ((hhm.sub (continuousOn_id.mul hβm)).abs)
    have ht : Tendsto (fun m => K * b * (m * betaF V₀c b m) -
        |hF V₀c b m - m * betaF V₀c b m|) (𝓝[>] 0)
        (𝓝 (K * b * (0 * betaF V₀c b 0) - |hF V₀c b 0 - 0 * betaF V₀c b 0|)) :=
      ((hf 0 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self).tendsto
    have := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun m (hm : 0 < m) =>
      sub_nonneg.2 (hpos b m hb hbb hm))
    linarith
  refine ⟨bbar, K, hbpos, hb2, hb3, hK0, hKb, h48, hall, fun b hb hbb => ?_, fun b m hb hbb hm => ?_⟩
  · have := hall b 0 hb hbb le_rfl
    simp only [zero_mul, sub_zero, mul_zero] at this
    exact abs_nonpos_iff.1 this
  · have h := hall b m hb hbb hm.le
    have hs1 := abs_s0R_le HF hb.le (by linarith) hm.le
    have hs : -1 < s0R V₀c b m := by have := (abs_le.1 hs1).1; linarith [hCb b hbb]
    have hβ := betaF_pos (V₀c := V₀c) hb hs
    have hKb' : K * b ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hbb hK0).trans hKb
    have hmβ : 0 < m * betaF V₀c b m := mul_pos hm hβ
    have := (abs_le.1 h).1
    nlinarith [mul_le_mul_of_nonneg_right hKb' hmβ.le]

/-! ### `cor:ward` (ii) -/

/-- Strict monotonicity of `b ↦ β(b, m²)` on `(0, b̄]` (from the uniform Lipschitz bound on
`s₀`). -/
theorem betaF_strictAnti (HF : FlowData d L A ℓ₀ V₀c lbar C κ) {c : ℝ} (hc2 : c ≤ lbar / 2)
    (h48 : 48 * C * c ≤ 1) {m : ℝ} (hm : 0 ≤ m) :
    StrictAntiOn (fun b => betaF V₀c b m) (Set.Ioc 0 c) := by
  intro b hb b' hb' hbb'
  have hC := HF.C_nonneg
  have hl := HF.lbar_pos
  have hs := abs_s0R_le HF hb.1.le (by linarith [hb.2]) hm
  have hs' := abs_s0R_le HF hb'.1.le (by linarith [hb'.2]) hm
  have hlip := s0R_lip HF hm hb.1.le (by linarith [hb.2]) hb'.1.le (by linarith [hb'.2])
  rw [abs_of_pos (sub_pos.2 hbb')] at hlip
  have hCc : 6 * C * c ≤ 1 / 8 := by linarith
  have hCb : 2 * C * b ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left hb.2 hC]
  have hCb' : 2 * C * b' ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left hb'.2 hC]
  set u := 1 + s0R V₀c b m
  set u' := 1 + s0R V₀c b' m
  have hu1 : 1 / 2 ≤ u := by have := (abs_le.1 hs).1; linarith
  have hu2 : u ≤ 3 / 2 := by have := (abs_le.1 hs).2; linarith
  have hu1' : 1 / 2 ≤ u' := by have := (abs_le.1 hs').1; linarith
  have hu2' : u' ≤ 3 / 2 := by have := (abs_le.1 hs').2; linarith
  have hd : |u' - u| ≤ 2 * C * (b' - b) := by simpa [u, u'] using hlip
  have hsq : u' ^ 2 ≤ u ^ 2 + 3 * (2 * C * (b' - b)) := by
    have e : u' ^ 2 = u ^ 2 + (u' - u) * (u' + u) := by ring
    have h1 : (u' - u) * (u' + u) ≤ |u' - u| * 3 := by
      calc (u' - u) * (u' + u) ≤ |(u' - u) * (u' + u)| := le_abs_self _
        _ = |u' - u| * (u' + u) := by rw [abs_mul, abs_of_pos (show 0 < u' + u by linarith)]
        _ ≤ |u' - u| * 3 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    rw [e]
    linarith [mul_le_mul_of_nonneg_right hd (by norm_num : (0 : ℝ) ≤ 3)]
  have hb0 := hb.1
  have hb0' := hb'.1
  show u' ^ 2 / b' < u ^ 2 / b
  rw [div_lt_div_iff₀ hb0' hb0]
  have hbc : b * (6 * C * (b' - b)) ≤ (b' - b) / 8 := by
    have : 6 * C * b ≤ 1 / 8 := by nlinarith [mul_le_mul_of_nonneg_left hb.2 hC]
    nlinarith [sub_pos.2 hbb']
  have hu2sq : 1 / 4 ≤ u ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hu2sq (sub_pos.2 hbb').le,
    mul_le_mul_of_nonneg_left hsq hb0.le, hbc]

/-- **`cor:ward` (ii)** for a given `V₀c` with `FlowDataW`: solutions `(b̃, m̃²)` of
`β(b̃, m̃²) = β`, `h(b̃, m̃²) = h` for `β ≥ β₀`, `h ≥ 0`, right-continuous at `h = 0`, and the
uniqueness at `h = 0`. -/
theorem cor_ward_ii (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) {bbar K : ℝ}
    (hbpos : 0 < bbar) (hb2 : bbar ≤ lbar / 2) (hK0 : 0 ≤ K) (hKb : K * bbar ≤ 1 / 2)
    (h48 : 48 * C * bbar ≤ 1)
    (hall : ∀ b m, 0 < b → b ≤ bbar → 0 ≤ m →
      |hF V₀c b m - m * betaF V₀c b m| ≤ K * b * (m * betaF V₀c b m))
    (hh0 : ∀ b, 0 < b → b ≤ bbar → hF V₀c b 0 = 0) :
    ∃ (β₀ : ℝ) (bt mt : ℝ → ℝ → ℝ), 0 < β₀ ∧ ∀ β, β₀ ≤ β → ∀ h, 0 ≤ h →
      0 < bt β h ∧ bt β h ≤ bbar ∧ 0 ≤ mt β h ∧ (0 < h → 0 < mt β h) ∧
      betaF V₀c (bt β h) (mt β h) = β ∧ hF V₀c (bt β h) (mt β h) = h ∧
      mt β 0 = 0 ∧ Tendsto (mt β) (𝓝[≥] 0) (𝓝 0) ∧ Tendsto (bt β) (𝓝[≥] 0) (𝓝 (bt β 0)) ∧
      (∀ b, 0 < b → b ≤ bbar → betaF V₀c b 0 = β → b = bt β 0) := by
  have HF := HW.toFlowData
  have hC := HF.C_nonneg
  have hl := HF.lbar_pos
  obtain ⟨hβc, hhc⟩ := betaF_hF_cont HF
  have hsub : Set.Ioc 0 bbar ×ˢ Set.Ici (0 : ℝ) ⊆ Set.Ioo 0 lbar ×ˢ Set.Ici 0 :=
    Set.prod_mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩) subset_rfl
  have hsb : ∀ b m, 0 < b → b ≤ bbar → 0 ≤ m → -(1 / 2) ≤ s0R V₀c b m ∧ s0R V₀c b m ≤ 1 / 2 :=
    fun b m hb hbb hm => by
      have hs := abs_s0R_le HF hb.le (by linarith) hm
      have : 2 * C * b ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left hbb hC]
      constructor <;> linarith [(abs_le.1 hs).1, (abs_le.1 hs).2]
  refine ivt_solution (lo := 1 / 4) (hi := 9 / 4) hbpos (by norm_num) (by norm_num)
    (hβc.mono hsub) (hhc.mono hsub) (fun m hm => betaF_strictAnti HF hb2 h48 hm) ?_ hh0 ?_
  · intro b m hb hbb hm
    obtain ⟨h1, h2⟩ := hsb b m hb hbb hm
    unfold betaF
    constructor
    · exact div_le_div_of_nonneg_right (by nlinarith) hb.le
    · exact div_le_div_of_nonneg_right (by nlinarith) hb.le
  · intro b m hb hbb hm
    have h := hall b m hb hbb hm
    obtain ⟨h1, -⟩ := hsb b m hb hbb hm
    have hβ := betaF_pos (V₀c := V₀c) (m := m) hb (by linarith)
    have hmβ : 0 ≤ m * betaF V₀c b m := mul_nonneg hm hβ.le
    have hKb' : K * b ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hbb hK0).trans hKb
    have := (abs_le.1 h).1
    nlinarith [mul_le_mul_of_nonneg_right hKb' hmβ]


/-- The conclusion of `cor:ward` (ii) at a fixed `β`. -/
def SolAt (V₀c : ℝ → ℂ → Vcoup) (bbar : ℝ) (bt mt : ℝ → ℝ → ℝ) (β : ℝ) : Prop :=
  ∀ h, 0 ≤ h →
    0 < bt β h ∧ bt β h ≤ bbar ∧ 0 ≤ mt β h ∧ (0 < h → 0 < mt β h) ∧
    betaF V₀c (bt β h) (mt β h) = β ∧ hF V₀c (bt β h) (mt β h) = h ∧
    mt β 0 = 0 ∧ Tendsto (mt β) (𝓝[≥] 0) (𝓝 0) ∧ Tendsto (bt β) (𝓝[≥] 0) (𝓝 (bt β 0)) ∧
    (∀ b, 0 < b → b ≤ bbar → betaF V₀c b 0 = β → b = bt β 0)

end

end Ward
