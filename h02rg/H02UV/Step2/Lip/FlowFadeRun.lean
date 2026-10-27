import Step2.Lip.FlowLipMain

/-!
# Fading memory: the error recursion with weighted histories

The Lipschitz chain `FlowLip*` bounds the errors of the normalised states along two histories
by the *unweighted* past distance `M ≥ dist3(t_i, t'_i)`, `i < j`. For the strict monotonicity of
`b ↦ ǧ_N` (`Flow2.Hist.MonoHyp`) the history enters with a *fading memory*:
`(3/4)^{j-1-i} dist3(t_i, t'_i) ≤ M`, i.e. `dist3(t_i, t'_i) ≤ m_{i+1}` with
`m_k = M (4/3)^{j-k}`.

The errors are generated with geometric decay (the covariance differences with ratio `1/2`,
`prop_C5_lip`; the `𝒲^lin` and zero-mode recursions with ratio `q ≤ 1/2`), so the bounds
`ev_k ≤ V m_k`, `eW_k ≤ W m_k`, `ew_k ≤ Z m_k` close for `k ≤ j` (`run_errors_w`), with
constants changed only by numerical factors (`err_rec_w`, `err_consts_w`). At `k = j` they are the
bounds of `run_errors` with `M` the weighted distance.

* `err_rec_w`, `err_consts_w`: the abstract weighted recursion and the choice of constants;
* `lD_sq_le_w`: the field scale of the covariance difference under weighted coupling errors;
* `run_step_w`: `run_step` with the covariance bound as a hypothesis;
* `run_errors_w`: the errors along two histories with fading memory.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

/-! ### The abstract weighted recursion -/

theorem err_rec_w {a₀ a₁ η q b V W Z : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hη : 0 ≤ η)
    (hq : 0 ≤ q) (hb : 0 ≤ b) (hV : 0 ≤ V) (hW : 0 ≤ W) (hZ : 0 ≤ Z)
    (c1 : a₀ + 4 / 3 * (a₁ * W + η * (5 / 2 * V + Z)) ≤ V)
    (c2 : 4 / 3 * q * W + η * (1 + 4 / 3 * (5 / 2 * V + Z)) ≤ W)
    (c3 : 4 / 3 * (q * Z + b * (5 / 2 * V)) ≤ Z) {j : ℕ} (m : ℕ → ℝ) (hm0 : ∀ k, 0 ≤ m k)
    (hmk : ∀ k < j, m k ≤ 4 / 3 * m (k + 1)) (v w z : ℕ → ℝ)
    (h0 : v 0 = 0 ∧ w 0 = 0 ∧ z 0 = 0)
    (hstep : ∀ k < j, (∀ i ≤ k, v i ≤ V * m i) →
      v (k + 1) ≤ a₀ * m (k + 1) + a₁ * w k + η * (v k + z k + 2 * V * m (k + 1)) ∧
      w (k + 1) ≤ q * w k + η * (m (k + 1) + v k + z k + 2 * V * m (k + 1)) ∧
      z (k + 1) ≤ q * z k + b * (v k + 2 * V * m (k + 1))) :
    ∀ k ≤ j, (∀ i ≤ k, v i ≤ V * m i) ∧ w k ≤ W * m k ∧ z k ≤ Z * m k := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun i hi => ?_, ?_, ?_⟩
    · rw [Nat.le_zero.1 hi, h0.1]; exact mul_nonneg hV (hm0 0)
    · rw [h0.2.1]; exact mul_nonneg hW (hm0 0)
    · rw [h0.2.2]; exact mul_nonneg hZ (hm0 0)
  | succ k ih =>
    intro hk
    obtain ⟨hv, hw, hz⟩ := ih (by omega)
    obtain ⟨s1, s2, s3⟩ := hstep k (by omega) hv
    have hvk := hv k le_rfl
    have hmm := hmk k (by omega)
    have hm1 := hm0 (k + 1)
    -- the bounds at `k` in terms of `m (k+1)`
    have bv : v k ≤ V * (4 / 3 * m (k + 1)) := hvk.trans (mul_le_mul_of_nonneg_left hmm hV)
    have bw : w k ≤ W * (4 / 3 * m (k + 1)) := hw.trans (mul_le_mul_of_nonneg_left hmm hW)
    have bz : z k ≤ Z * (4 / 3 * m (k + 1)) := hz.trans (mul_le_mul_of_nonneg_left hmm hZ)
    have e1 : v (k + 1) ≤ V * m (k + 1) := by
      refine s1.trans ?_
      have a1 := mul_le_mul_of_nonneg_left bw ha₁
      have a2 : η * (v k + z k + 2 * V * m (k + 1)) ≤
          η * (V * (4 / 3 * m (k + 1)) + Z * (4 / 3 * m (k + 1)) + 2 * V * m (k + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith only [bv, bz]) hη
      have a3 := mul_le_mul_of_nonneg_right c1 hm1
      linarith only [a1, a2, a3, show (a₀ + 4 / 3 * (a₁ * W + η * (5 / 2 * V + Z))) * m (k + 1) =
        a₀ * m (k + 1) + a₁ * (W * (4 / 3 * m (k + 1))) +
          η * (V * (4 / 3 * m (k + 1)) + Z * (4 / 3 * m (k + 1)) + 2 * V * m (k + 1)) by ring]
    refine ⟨fun i hi => ?_, ?_, ?_⟩
    · rcases Nat.lt_or_ge i (k + 1) with h | h
      · exact hv i (by omega)
      · rw [show i = k + 1 by omega]; exact e1
    · refine s2.trans ?_
      have a1 := mul_le_mul_of_nonneg_left bw hq
      have a2 : η * (m (k + 1) + v k + z k + 2 * V * m (k + 1)) ≤
          η * (m (k + 1) + V * (4 / 3 * m (k + 1)) + Z * (4 / 3 * m (k + 1)) + 2 * V * m (k + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith only [bv, bz]) hη
      have a3 := mul_le_mul_of_nonneg_right c2 hm1
      linarith only [a1, a2, a3, show (4 / 3 * q * W + η * (1 + 4 / 3 * (5 / 2 * V + Z))) * m (k + 1) =
        q * (W * (4 / 3 * m (k + 1))) +
          η * (m (k + 1) + V * (4 / 3 * m (k + 1)) + Z * (4 / 3 * m (k + 1)) + 2 * V * m (k + 1))
        by ring]
    · refine s3.trans ?_
      have a1 := mul_le_mul_of_nonneg_left bz hq
      have a2 : b * (v k + 2 * V * m (k + 1)) ≤ b * (V * (4 / 3 * m (k + 1)) + 2 * V * m (k + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith only [bv]) hb
      have a3 := mul_le_mul_of_nonneg_right c3 hm1
      linarith only [a1, a2, a3, show 4 / 3 * (q * Z + b * (5 / 2 * V)) * m (k + 1) =
        q * (Z * (4 / 3 * m (k + 1))) + b * (V * (4 / 3 * m (k + 1)) + 2 * V * m (k + 1)) by ring]

/-- **Choice of the constants** in `err_rec_w`: for `q ≤ 1/2` and `η` small, `V = 2a₀ + 1`,
`Z = 10bV`, `W = 3η(1 + 4V + 2Z)` close. -/
theorem err_consts_w {a₀ a₁ η q b : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁) (hη : 0 ≤ η) (hq : 0 ≤ q)
    (hq2 : q ≤ 1 / 2) (hb : 0 ≤ b)
    (hsmall : η * (4 * a₁ * (1 + 4 * (2 * a₀ + 1) + 2 * (10 * b * (2 * a₀ + 1))) +
      (4 * (2 * a₀ + 1) + 2 * (10 * b * (2 * a₀ + 1)))) ≤ 1 / 2) :
    a₀ + 4 / 3 * (a₁ * (3 * η * (1 + 4 * (2 * a₀ + 1) + 2 * (10 * b * (2 * a₀ + 1)))) +
        η * (5 / 2 * (2 * a₀ + 1) + 10 * b * (2 * a₀ + 1))) ≤ 2 * a₀ + 1 ∧
      4 / 3 * q * (3 * η * (1 + 4 * (2 * a₀ + 1) + 2 * (10 * b * (2 * a₀ + 1)))) +
        η * (1 + 4 / 3 * (5 / 2 * (2 * a₀ + 1) + 10 * b * (2 * a₀ + 1))) ≤
        3 * η * (1 + 4 * (2 * a₀ + 1) + 2 * (10 * b * (2 * a₀ + 1))) ∧
      4 / 3 * (q * (10 * b * (2 * a₀ + 1)) + b * (5 / 2 * (2 * a₀ + 1))) ≤
        10 * b * (2 * a₀ + 1) := by
  obtain ⟨V, hVd⟩ : ∃ V, V = 2 * a₀ + 1 := ⟨_, rfl⟩
  obtain ⟨Z, hZd⟩ : ∃ Z, Z = 10 * b * V := ⟨_, rfl⟩
  rw [← hVd, ← hZd] at hsmall ⊢
  have hV : 0 ≤ V := by rw [hVd]; positivity
  have hZ : 0 ≤ Z := by rw [hZd]; positivity
  have hP : 0 ≤ 1 + 4 * V + 2 * Z := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have h1 : η * (5 / 2 * V + Z) ≤ η * (4 * V + 2 * Z) * (3 / 4) :=
      by nlinarith [mul_nonneg hη hV, mul_nonneg hη hZ]
    have e1 : 4 / 3 * (a₁ * (3 * η * (1 + 4 * V + 2 * Z)) + η * (5 / 2 * V + Z)) =
        η * (4 * a₁ * (1 + 4 * V + 2 * Z)) + 4 / 3 * (η * (5 / 2 * V + Z)) := by ring
    have e2 : η * (4 * a₁ * (1 + 4 * V + 2 * Z) + (4 * V + 2 * Z)) =
        η * (4 * a₁ * (1 + 4 * V + 2 * Z)) + η * (4 * V + 2 * Z) := by ring
    rw [e1]
    linarith only [h1, e2, hsmall, hVd, ha₀]
  · have h1 : 4 / 3 * q * (3 * η * (1 + 4 * V + 2 * Z)) ≤ 2 / 3 * (3 * η * (1 + 4 * V + 2 * Z)) := by
      have : 4 / 3 * q ≤ 2 / 3 := by linarith only [hq2]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have h2 : η * (1 + 4 / 3 * (5 / 2 * V + Z)) ≤ η * (1 + 4 * V + 2 * Z) :=
      mul_le_mul_of_nonneg_left (by linarith only [hV, hZ]) hη
    linarith only [h1, h2]
  · have h1 : 4 / 3 * (q * Z) ≤ 2 / 3 * Z := by nlinarith
    have h2 : 4 / 3 * (b * (5 / 2 * V)) = Z / 3 := by rw [hZd]; ring
    linarith only [h1, h2, show 4 / 3 * (q * Z + b * (5 / 2 * V)) = 4 / 3 * (q * Z) +
      4 / 3 * (b * (5 / 2 * V)) by ring]

/-! ### The covariance difference under weighted errors -/

theorem geom_two_thirds (n : ℕ) : ∑ i ∈ range n, (2 / 3 : ℝ) ^ i ≤ 3 - 3 * (2 / 3) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, pow_succ]
    linarith

theorem geom_w_sum (k : ℕ) :
    ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) * (4 / 3) ^ (k - i) ≤ 3 := by
  have e : ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) * (4 / 3) ^ (k - i) =
      ∑ i ∈ range (k + 1), (2 / 3 : ℝ) ^ (k - i) := by
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_pow]; norm_num
  have e2 : ∑ i ∈ range (k + 1), (2 / 3 : ℝ) ^ (k - i) = ∑ i ∈ range (k + 1), (2 / 3 : ℝ) ^ i :=
    sum_range_reflect (fun i => (2 / 3 : ℝ) ^ i) (k + 1)
  rw [e, e2]
  have := geom_two_thirds (k + 1)
  have : (0 : ℝ) ≤ 3 * (2 / 3) ^ (k + 1) := by positivity
  linarith

variable {L N : ℕ} [NeZero L]

section Def

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `lD² ≤ 3 K_c L⁸ V X` if `|δζ_i| ≤ V X (4/3)^{k-i}` for `i ≤ k`. -/
theorem lD_sq_le_w {Kc V X : ℝ} (hKc : 0 ≤ Kc) (hV : 0 ≤ V) (hX : 0 ≤ X) (k : ℕ)
    (t t' : Hist.Seq (Xs R)) (h : ∀ i ≤ k, eζH R i t t' ≤ V * (X * (4 / 3) ^ (k - i))) :
    lD R Kc k t t' ^ 2 ≤ 3 * Kc * (L : ℝ) ^ 8 * (V * X) := by
  have hS0 : 0 ≤ ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) * eζH R i t t' :=
    sum_nonneg fun i _ => mul_nonneg (by positivity) (norm_nonneg _)
  rw [lD, ellLip_two_sq L (mul_nonneg hKc hS0)]
  have hS : ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) * eζH R i t t' ≤ 3 * (V * X) := by
    calc ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) * eζH R i t t'
        ≤ ∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) * (4 / 3) ^ (k - i) * (V * X) :=
          sum_le_sum fun i hi => by
            have := mul_le_mul_of_nonneg_left (h i (by have := mem_range.1 hi; omega))
              (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (k - i))
            linarith only [this, show (1 / 2 : ℝ) ^ (k - i) * (V * (X * (4 / 3) ^ (k - i))) =
              (1 / 2 : ℝ) ^ (k - i) * (4 / 3) ^ (k - i) * (V * X) by ring]
      _ = (∑ i ∈ range (k + 1), (1 / 2 : ℝ) ^ (k - i) * (4 / 3) ^ (k - i)) * (V * X) := by
          rw [sum_mul]
      _ ≤ 3 * (V * X) := mul_le_mul_of_nonneg_right (geom_w_sum k) (mul_nonneg hV hX)
  have e8 : (L : ℝ) ^ (2 * pPhi 2) = (L : ℝ) ^ 8 := by simp [pPhi]
  rw [e8]
  have hL : (0 : ℝ) ≤ (L : ℝ) ^ 8 := by positivity
  have := mul_le_mul_of_nonneg_left hS hKc
  have := mul_le_mul_of_nonneg_right this hL
  linarith only [this, show Kc * (3 * (V * X)) * (L : ℝ) ^ 8 = 3 * Kc * (L : ℝ) ^ 8 * (V * X) by ring]

end Def

section Step

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

set_option maxHeartbeats 1000000 in
/-- **One step of the error recursion.** -/
theorem run_step_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {k : ℕ} (hk : k < j) {M V : ℝ}
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hd : Hist.dist3 (t k) (t' k) ≤ M)
    (hΔ : lD R Kc k t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * (V * M)) {Cq Cl cS C₀ C₂ : ℝ} (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂)
    (hβ : 0 ≤ bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
    (hkap : ∀ i : Fin 4, cwt L k i * ‖(kapH R k t' i - kapH R k t i) -
          (SD.shv R k (sdH R k t') i - SD.shv R k (sdH R k t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (cIn R (cx κ cT) k t t') (lD R Kc k t t') 1 (R.ℓ / 4))
    (hW : Fnorm (k + 1) R.ℓ (nWlH R k t' - nWlH R k t) ≤
        ENNReal.ofReal (4 * (4 * C₂ * e ^ 2) * relDist e (aIn R k t t') 0 0 (lD R Kc k t t') 1
          (R.ℓ / 4) + 4 * (2 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) * ((cw + 1) * ε ^ 2)) *
            (bWIn R cw k t t' / ((cw + 1) * ε ^ 2) + lD R Kc k t t' ^ 2 / (1 * (R.ℓ / 4)) ^ 2))) :
    let β := bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2
    let Λ0 := 2 * Kc * (L : ℝ) ^ 8
    let κW := C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)
    evH R (k + 1) t t' ≤ ka0 R.ℓ β * M + 8 * β * eWH R k t t' + (e + ε) *
        (kEv R.ℓ β (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) * evH R k t t' +
          kEw R.ℓ β (cmu Λ cm) * ewH R k t t' + kEV R.ℓ β Λ0 * (V * M)) ∧
      eWH R (k + 1) t t' ≤ 8 * κW * eWH R k t t' + (e + ε) * (kWM R.ℓ C₂ * M +
        kWv R.ℓ C₂ κW cw (cmu Λ cm) * evH R k t t' + kWw R.ℓ C₂ (cmu Λ cm) * ewH R k t t' +
        kWV R.ℓ C₂ κW cw Λ0 * (V * M)) ∧
      ewH R (k + 1) t t' ≤ 9 / (8 * (L : ℝ) ^ 2) * ewH R k t t' +
        (2 * R.ℓ ^ 2 / (L : ℝ) ^ 2 + 9 * Λ0) * (evH R k t t' + V * M) := by
  intro β Λ0 κW
  have HC := H.cmp k hk.le
  have hℓ := HC.hℓ
  have he := HC.he
  have hε := H.hε0
  have hε1 := HC.hε1
  have hcmu := HC.hcmu
  have hcw := HC.hcw
  have hcx := HC.hcx
  obtain ⟨hdx, hdg, hdμ⟩ := dist3_parts hd
  have hζ := eζ_le_ev HC.H HC.H'
  have hev := evH_nonneg (R := R) (t := t) (t' := t') k
  have hew := ewH_nonneg (R := R) (t := t) (t' := t') k
  have hdn := H.dn_le hk.le
  have hΔ0 : 0 ≤ lD R Kc k t t' ^ 2 := sq_nonneg _
  have hΘ := thetaH_le HC
  have hcTh : 0 ≤ cTh R.ℓ cw (cx κ cT) := by
    unfold cTh; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  have hΛ0 : 0 ≤ Λ0 := by have := H.hKc; positivity
  refine ⟨?_, ?_, ?_⟩
  · -- couplings
    have h1 := ev_succ_le HC hkap
    have hG := ghat_sub_le (sdH R k t) (sdH R k t')
      (show |(t' k).1| ≤ 1 by rw [abs_of_pos HC.H'.g_pos]; exact HC.H'.g_le.trans hε1)
    have hγ : ‖ghat (sdH R k t)‖ ≤ 2 * ε := by
      have := norm_ghat_le (sdH R k t)
      have hg : |(sdH R k t).g| ≤ ε := by
        show |(t k).1| ≤ ε
        rw [abs_of_pos HC.H.g_pos]; exact HC.H.g_le
      linarith
    exact ev_rec hℓ hβ hcmu hcTh hΛ0 he.le H.he1 hε.le hε1 hM hV hev hew hdx hdg hdμ hζ hdn
      hΔ hΔ0 hΘ hG hγ (norm_nonneg _) h1
  · -- `𝒲^lin`
    have h1 := eW_succ_le HC hε hC₀ hC₂ hW
    have ha : aIn R k t t' ≤ (cM : ℝ) * R.ℓ ^ 2 * |(t' k).2.1 - (t k).2.1| +
        5 * R.ℓ ^ 4 * |(t' k).1 - (t k).1| + 8 * R.ℓ ^ 4 *
        ‖nCor ((t' k).2.1 : ℂ) (nW1H R k t') - nCor ((t k).2.1 : ℂ) (nW1H R k t)‖ +
        2 * cM * R.ℓ ^ 2 * evH R k t t' := by
      unfold aIn aVf
      have hM' : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
      have hℓ2 : (7 / 8 * R.ℓ) ^ 2 ≤ R.ℓ ^ 2 := by nlinarith
      have hℓ4 : (7 / 8 * R.ℓ) ^ 4 ≤ R.ℓ ^ 4 := by
        have : (7 / 8 * R.ℓ) ^ 4 = (7 / 8) ^ 4 * R.ℓ ^ 4 := by ring
        rw [this]; nlinarith [pow_pos hℓ 4]
      have hdn0 := norm_nonneg (nCor ((t' k).2.1 : ℂ) (nW1H R k t') - nCor ((t k).2.1 : ℂ)
        (nW1H R k t))
      have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ2 hM')
        (by positivity : (0 : ℝ) ≤ |(t' k).2.1 - (t k).2.1| + 2 * evH R k t t')
      have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ4 (by norm_num : (0 : ℝ) ≤ 4))
        (by positivity : (0 : ℝ) ≤ 8 / 7 * |(t' k).1 - (t k).1| + 2 *
          ‖nCor ((t' k).2.1 : ℂ) (nW1H R k t') - nCor ((t k).2.1 : ℂ) (nW1H R k t)‖)
      have h3 : 4 * R.ℓ ^ 4 * (8 / 7 * |(t' k).1 - (t k).1|) ≤ 5 * R.ℓ ^ 4 * |(t' k).1 - (t k).1| := by
        nlinarith [pow_pos hℓ 4, abs_nonneg ((t' k).1 - (t k).1)]
      nlinarith
    have hbW : bWIn R cw k t t' ≤ eWH R k t t' + 28 * cw * ε ^ 2 * evH R k t t' := by
      unfold bWIn
      have hg2 : (t k).1 ^ 2 ≤ ε ^ 2 := by have := HC.H.g_pos; have := HC.H.g_le; gcongr
      have := mul_le_mul hζ (mul_le_mul_of_nonneg_left hg2 hcw) (by positivity) hev
      nlinarith
    have hκW : 0 ≤ κW := by positivity
    exact eW_rec hℓ hC₂ hκW hcw hcmu hΛ0 he.le H.he1 hε.le hε1 hM hV hev hew hdg hdμ hζ hdn hΔ
      hΔ0 ha hbW h1
  · -- the zero mode
    have h1 := ew_succ_le HC
    have h2 := nW1H_sub_le HC.H HC.H' (H.whH_le hk.le)
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    exact ew_rec hL hΛ0 hev hew hM hV hζ h2 hΔ h1

end Step

/-- `m_k = M (4/3)^{j-k}`: the weighted bound at step `k` for target step `j`. -/
def mW (M : ℝ) (j k : ℕ) : ℝ := M * (4 / 3 : ℝ) ^ (j - k)

theorem mW_nonneg {M : ℝ} (hM : 0 ≤ M) (j k : ℕ) : 0 ≤ mW M j k := by unfold mW; positivity

theorem mW_succ {M : ℝ} {j k : ℕ} (hk : k < j) : mW M j k = 4 / 3 * mW M j (k + 1) := by
  unfold mW
  rw [show j - k = (j - (k + 1)) + 1 by omega, pow_succ]; ring

theorem mW_le {M : ℝ} {j k i : ℕ} (hik : i ≤ k) (hk : k ≤ j) :
    mW M j i = mW M j k * (4 / 3 : ℝ) ^ (k - i) := by
  unfold mW
  rw [show j - i = (j - k) + (k - i) by omega, pow_add]; ring

theorem mW_self (M : ℝ) (j : ℕ) : mW M j j = M := by simp [mW]

section Ind

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {j : ℕ} {t t' : Hist.Seq (Xs R)}
  {Λ κ cm cT ε cz cw e Kc : ℝ}

set_option maxHeartbeats 2000000 in
/-- **The errors along two histories with fading memory.** If the past distances satisfy
`dist3(t_i, t'_i) ≤ M (4/3)^{j-1-i}` for `i < j`, the errors at `k ≤ j` are bounded by
`m_k = M (4/3)^{j-k}` times the constants. -/
theorem run_errors_w (H : Run R j t t' Λ κ cm cT ε cz cw e Kc) {M V W Z : ℝ} (hM : 0 ≤ M)
    (hd : ∀ i < j, Hist.dist3 (t i) (t' i) ≤ mW M j (i + 1)) {Cq Cl cS C₀ C₂ : ℝ} (hC₀ : 0 ≤ C₀)
    (hC₂ : 0 ≤ C₂)
    (hβ : 0 ≤ bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
    (hkap : ∀ k < j, ∀ i : Fin 4, cwt L k i * ‖(kapH R k t' i - kapH R k t i) -
          (SD.shv R k (sdH R k t') i - SD.shv R k (sdH R k t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (cIn R (cx κ cT) k t t') (lD R Kc k t t') 1 (R.ℓ / 4))
    (hW : ∀ k < j, Fnorm (k + 1) R.ℓ (nWlH R k t' - nWlH R k t) ≤
        ENNReal.ofReal (4 * (4 * C₂ * e ^ 2) * relDist e (aIn R k t t') 0 0 (lD R Kc k t t') 1
          (R.ℓ / 4) + 4 * (2 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) * ((cw + 1) * ε ^ 2)) *
            (bWIn R cw k t t' / ((cw + 1) * ε ^ 2) + lD R Kc k t t' ^ 2 / (1 * (R.ℓ / 4)) ^ 2)))
    (hV : 0 ≤ V) (hW0 : 0 ≤ W) (hZ : 0 ≤ Z)
    (c1 : ka0 R.ℓ (bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2) +
      4 / 3 * (8 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 * W +
      (e + ε) * kAll R.ℓ (bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
        (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) C₂
        (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) cw * (5 / 2 * V + Z)) ≤ V)
    (c2 : 4 / 3 * (8 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) + 9 / (8 * (L : ℝ) ^ 2)) * W +
      (e + ε) * kAll R.ℓ (bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2)
        (cmu Λ cm) (cTh R.ℓ cw (cx κ cT)) (2 * Kc * (L : ℝ) ^ 8) C₂
        (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) cw * (1 + 4 / 3 * (5 / 2 * V + Z)) ≤ W)
    (c3 : 4 / 3 * ((8 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) + 9 / (8 * (L : ℝ) ^ 2)) * Z +
      (2 * R.ℓ ^ 2 / (L : ℝ) ^ 2 + 9 * (2 * Kc * (L : ℝ) ^ 8)) * (5 / 2 * V)) ≤ Z) :
    ∀ k ≤ j, (∀ i ≤ k, evH R i t t' ≤ V * mW M j i) ∧ eWH R k t t' ≤ W * mW M j k ∧
      ewH R k t t' ≤ Z * mW M j k := by
  set β := bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) 2 2 2 with hβd
  set Λ0 := 2 * Kc * (L : ℝ) ^ 8 with hΛd
  set κW := C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3) with hκd
  set cThv := cTh R.ℓ cw (cx κ cT) with hcd
  set ka := kAll R.ℓ β (cmu Λ cm) cThv Λ0 C₂ κW cw
  have hℓ : 0 < R.ℓ := Fact.out
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hκW : 0 ≤ κW := by positivity
  have hΛ0 : 0 ≤ Λ0 := by have := H.hKc; positivity
  have hcmu : 0 ≤ cmu Λ cm := ((H.cmp 0 (Nat.zero_le _))).hcmu
  have hcw : 0 ≤ cw := ((H.cmp 0 (Nat.zero_le _))).hcw
  have hcx : 0 ≤ cx κ cT := ((H.cmp 0 (Nat.zero_le _))).hcx
  have hcTh : 0 ≤ cThv := by
    unfold cThv cTh; have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := kAll_parts hℓ hβ hcmu hcTh hΛ0 hC₂ hκW hcw
  have hS : 0 ≤ e + ε := by linarith [(H.cmp 0 (Nat.zero_le _)).he, H.hε0]
  have hη : 0 ≤ (e + ε) * ka := by unfold ka kAll; positivity
  have ha0 : 0 ≤ ka0 R.ℓ β := by
    unfold ka0; have := kX_nonneg R.ℓ; have := (Real.exp_pos 1).le; positivity
  refine err_rec_w (a₀ := ka0 R.ℓ β) (a₁ := 8 * β) (η := (e + ε) * ka)
    (q := 8 * κW + 9 / (8 * (L : ℝ) ^ 2)) (b := 2 * R.ℓ ^ 2 / (L : ℝ) ^ 2 + 9 * Λ0) ha0
    (by positivity) hη (by positivity) (by positivity) hV hW0 hZ
    (by linarith only [c1, show 4 / 3 * (8 * β * W + (e + ε) * ka * (5 / 2 * V + Z)) =
      4 / 3 * (8 * β * W + (e + ε) * ka * (5 / 2 * V + Z)) by ring])
    (by linarith only [c2, show (e + ε) * ka * (1 + 4 / 3 * (5 / 2 * V + Z)) =
      (e + ε) * ka * (1 + 4 / 3 * (5 / 2 * V + Z)) by ring]) c3
    (mW M j) (mW_nonneg hM j) (fun k hk => le_of_eq (mW_succ hk))
    (fun k => evH R k t t') (fun k => eWH R k t t') (fun k => ewH R k t t') errs_zero ?_
  intro k hk hIH
  have hm' := mW_nonneg hM j (k + 1)
  have hVm : 0 ≤ 2 * V * mW M j (k + 1) := by positivity
  -- the covariance difference
  have hζIH : ∀ i ≤ k, eζH R i t t' ≤ V * (mW M j k * (4 / 3) ^ (k - i)) := fun i hi => by
    rw [← mW_le hi hk.le]
    exact (eζ_le_ev (H.cmp i (by omega)).H (H.cmp i (by omega)).H').trans (hIH i hi)
  have hΔ0 := lD_sq_le_w H.hKc hV (mW_nonneg hM j k) k t t' hζIH
  have hΔ : lD R Kc k t t' ^ 2 ≤ 2 * Kc * (L : ℝ) ^ 8 * ((2 * V) * mW M j (k + 1)) := by
    rw [mW_succ hk] at hΔ0
    linarith only [hΔ0, show 3 * Kc * (L : ℝ) ^ 8 * (V * (4 / 3 * mW M j (k + 1))) =
      2 * Kc * (L : ℝ) ^ 8 * ((2 * V) * mW M j (k + 1)) by ring]
  have hdk : Hist.dist3 (t k) (t' k) ≤ mW M j (k + 1) := hd k hk
  obtain ⟨s1, s2, s3⟩ := run_step_w H hk hm' (by positivity : (0 : ℝ) ≤ 2 * V) hdk hΔ hC₀ hC₂ hβ
    (hkap k hk) (hW k hk)
  simp only [← hβd, ← hΛd, ← hκd, ← hcd] at s1 s2 s3
  have hev := evH_nonneg (R := R) (t := t) (t' := t') k
  have hew := ewH_nonneg (R := R) (t := t) (t' := t') k
  have heW : 0 ≤ eWH R k t t' := eWH_nonneg R k t t'
  have eVM : 2 * V * mW M j (k + 1) = (2 * V) * mW M j (k + 1) := by ring
  rw [← eVM] at s1 s2 s3
  refine ⟨s1.trans ?_, s2.trans ?_, s3.trans ?_⟩
  · have : kEv R.ℓ β (cmu Λ cm) cThv * evH R k t t' + kEw R.ℓ β (cmu Λ cm) * ewH R k t t' +
        kEV R.ℓ β Λ0 * (2 * V * mW M j (k + 1)) ≤
        ka * (evH R k t t' + ewH R k t t' + 2 * V * mW M j (k + 1)) := by
      have a1 : kEv R.ℓ β (cmu Λ cm) cThv ≤ ka := by unfold ka kAll; linarith
      have a2 : kEw R.ℓ β (cmu Λ cm) ≤ ka := by unfold ka kAll; linarith
      have a3 : kEV R.ℓ β Λ0 ≤ ka := by unfold ka kAll; linarith
      nlinarith [mul_le_mul_of_nonneg_right a1 hev, mul_le_mul_of_nonneg_right a2 hew,
        mul_le_mul_of_nonneg_right a3 hVm]
    have h1 := mul_le_mul_of_nonneg_left this hS
    have e1 : (e + ε) * ka * (evH R k t t' + ewH R k t t' + 2 * V * mW M j (k + 1)) =
        (e + ε) * (ka * (evH R k t t' + ewH R k t t' + 2 * V * mW M j (k + 1))) := by ring
    show _ ≤ ka0 R.ℓ β * mW M j (k + 1) + 8 * β * eWH R k t t' +
      (e + ε) * ka * (evH R k t t' + ewH R k t t' + 2 * V * mW M j (k + 1))
    linarith only [h1, e1]
  · have : kWM R.ℓ C₂ * mW M j (k + 1) + kWv R.ℓ C₂ κW cw (cmu Λ cm) * evH R k t t' +
        kWw R.ℓ C₂ (cmu Λ cm) * ewH R k t t' + kWV R.ℓ C₂ κW cw Λ0 * (2 * V * mW M j (k + 1)) ≤
        ka * (mW M j (k + 1) + evH R k t t' + ewH R k t t' + 2 * V * mW M j (k + 1)) := by
      have a1 : kWM R.ℓ C₂ ≤ ka := by unfold ka kAll; linarith
      have a2 : kWv R.ℓ C₂ κW cw (cmu Λ cm) ≤ ka := by unfold ka kAll; linarith
      have a3 : kWw R.ℓ C₂ (cmu Λ cm) ≤ ka := by unfold ka kAll; linarith
      have a4 : kWV R.ℓ C₂ κW cw Λ0 ≤ ka := by unfold ka kAll; linarith
      nlinarith [mul_le_mul_of_nonneg_right a1 hm', mul_le_mul_of_nonneg_right a2 hev,
        mul_le_mul_of_nonneg_right a3 hew, mul_le_mul_of_nonneg_right a4 hVm]
    have h1 := mul_le_mul_of_nonneg_left this hS
    have h2 : 8 * κW * eWH R k t t' ≤ (8 * κW + 9 / (8 * (L : ℝ) ^ 2)) * eWH R k t t' :=
      mul_le_mul_of_nonneg_right (by have : 0 ≤ 9 / (8 * (L : ℝ) ^ 2) := by positivity
                                     linarith) heW
    have e1 : (e + ε) * ka * (mW M j (k + 1) + evH R k t t' + ewH R k t t' +
        2 * V * mW M j (k + 1)) = (e + ε) * (ka * (mW M j (k + 1) + evH R k t t' + ewH R k t t' +
        2 * V * mW M j (k + 1))) := by ring
    show _ ≤ (8 * κW + 9 / (8 * (L : ℝ) ^ 2)) * eWH R k t t' +
      (e + ε) * ka * (mW M j (k + 1) + evH R k t t' + ewH R k t t' + 2 * V * mW M j (k + 1))
    linarith only [h1, h2, e1]
  · have h2 : 9 / (8 * (L : ℝ) ^ 2) * ewH R k t t' ≤
        (8 * κW + 9 / (8 * (L : ℝ) ^ 2)) * ewH R k t t' :=
      mul_le_mul_of_nonneg_right (by linarith) hew
    linarith

end Ind

end

end Step2
