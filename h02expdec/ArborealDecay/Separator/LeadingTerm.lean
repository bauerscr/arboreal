module

public import Mathlib

/-!
# Leading term at infinity (supplement `lem:L8`)

Let `N, Q` be real polynomials with `N ≠ 0` and `deg N < deg Q`. If `Im (N(z) / Q(z)) ≤ 0` for
every `z` in the open upper half-plane, then `deg Q = deg N + 1`.

(Lean's division by zero gives `0`, so the hypothesis at zeros of `Q` is automatic; this is the
supplement's statement with `R₀ = 0`, which is the form used in `thm:separator`.)
-/

@[expose] public section

open Polynomial Filter Topology Asymptotics Bornology

namespace ArborealDecay.Separator

noncomputable section

/-- For `k ≥ 2` there are points of the open upper half-plane whose `k`-th power is `I`, resp.
`-I`. -/
theorem exists_upper_pow_eq (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ∃ w : ℂ, 0 < w.im ∧ w ^ k = (ε : ℂ) * Complex.I := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  rcases hε with rfl | rfl
  · refine ⟨Complex.exp ((Real.pi / (2 * k) : ℝ) * Complex.I), ?_, ?_⟩
    · rw [Complex.exp_ofReal_mul_I_im]
      apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
      rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
    · rw [← Complex.exp_nat_mul]
      have : (k : ℂ) * ((Real.pi / (2 * k) : ℝ) * Complex.I) = Real.pi / 2 * Complex.I := by
        push_cast; field_simp
      rw [this, Complex.exp_pi_div_two_mul_I]; simp
  · refine ⟨Complex.exp ((3 * Real.pi / (2 * k) : ℝ) * Complex.I), ?_, ?_⟩
    · rw [Complex.exp_ofReal_mul_I_im]
      apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
      rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
    · rw [← Complex.exp_nat_mul]
      have : (k : ℂ) * ((3 * Real.pi / (2 * k) : ℝ) * Complex.I) =
          -Real.pi / 2 * Complex.I + 2 * Real.pi * Complex.I := by
        push_cast; field_simp; ring
      rw [this, Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]
      rw [show (2 * Real.pi * Complex.I : ℂ) = ((1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I) by simp,
        Complex.exp_nat_mul_two_pi_mul_I]
      simp

/-- `z ^ k N(z) / Q(z) → lc N / lc Q` at infinity in `ℂ` when `deg Q = deg N + k`. -/
theorem tendsto_pow_mul_div_cobounded {N Q : ℂ[X]} (hQ : Q ≠ 0) (k : ℕ)
    (hdeg : Q.natDegree = N.natDegree + k) :
    Tendsto (fun z => z ^ k * N.eval z / Q.eval z) (cobounded ℂ)
      (𝓝 (N.leadingCoeff / Q.leadingCoeff)) := by
  have hN := (isEquivalent_cobounded_leading_monomial (P := N))
  have hQe := (isEquivalent_cobounded_leading_monomial (P := Q))
  have hκ : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  have h1 := ((IsEquivalent.refl (u := fun z : ℂ => z ^ k)).mul hN).div hQe
  refine h1.symm.tendsto_nhds ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) 1] with z hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  simp only [Pi.div_apply, Pi.mul_apply, hdeg, pow_add]
  field_simp

/-- Lemma L8. -/
theorem natDegree_eq_succ_of_im_nonpos {N Q : ℝ[X]} (hN : N ≠ 0)
    (hdeg : N.natDegree < Q.natDegree)
    (him : ∀ z : ℂ, 0 < z.im → (aeval z N / aeval z Q).im ≤ 0) :
    Q.natDegree = N.natDegree + 1 := by
  by_contra hne
  set k := Q.natDegree - N.natDegree with hk
  have hk2 : 2 ≤ k := by omega
  have hQ : Q ≠ 0 := by rintro rfl; simp at hdeg
  set NC := N.map Complex.ofRealHom
  set QC := Q.map Complex.ofRealHom
  have hNC : NC.natDegree = N.natDegree := natDegree_map_eq_of_injective
    Complex.ofRealHom.injective _
  have hQC : QC.natDegree = Q.natDegree := natDegree_map_eq_of_injective
    Complex.ofRealHom.injective _
  have hQC0 : QC ≠ 0 := (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hQ
  have hlim := tendsto_pow_mul_div_cobounded hQC0 k (by rw [hNC, hQC]; omega)
  have hlcN : NC.leadingCoeff = (N.leadingCoeff : ℂ) := leadingCoeff_map_of_injective
    Complex.ofRealHom.injective _
  have hlcQ : QC.leadingCoeff = (Q.leadingCoeff : ℂ) := leadingCoeff_map_of_injective
    Complex.ofRealHom.injective _
  set r : ℝ := N.leadingCoeff / Q.leadingCoeff with hr
  have hr0 : r ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hN) (leadingCoeff_ne_zero.mpr hQ)
  rw [hlcN, hlcQ, ← Complex.ofReal_div] at hlim
  have hev : ∀ z : ℂ, aeval z N = NC.eval z := fun z => by rw [aeval_def, eval₂_eq_eval_map]; rfl
  have hevQ : ∀ z : ℂ, aeval z Q = QC.eval z := fun z => by rw [aeval_def, eval₂_eq_eval_map]; rfl
  -- choose the ray
  obtain ⟨ε, hε, hpos⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ 0 < -r / ε := by
    rcases lt_or_gt_of_ne hr0 with h | h
    · exact ⟨1, Or.inl rfl, by simp; linarith⟩
    · exact ⟨-1, Or.inr rfl, by simp; linarith⟩
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨w, hw, hwk⟩ := exists_upper_pow_eq k hk2 ε hε
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hray : Tendsto (fun ρ : ℝ => (ρ : ℂ) * w) atTop (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    refine (tendsto_id.atTop_mul_const hnw).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with ρ hρ
    simp [abs_of_nonneg hρ]
  set h : ℂ → ℂ := fun z => z ^ k * NC.eval z / QC.eval z
  have hre : Tendsto (fun ρ : ℝ => -(h ((ρ : ℂ) * w)).re / ε) atTop (𝓝 (-r / ε)) := by
    have := ((Complex.continuous_re.tendsto _).comp (hlim.comp hray))
    simpa using (this.neg.div_const ε)
  have hev_pos := hre.eventually (eventually_gt_nhds hpos)
  obtain ⟨ρ, hρ, hρ1⟩ := (hev_pos.and (eventually_gt_atTop 0)).exists
  -- contradiction with the hypothesis at `z = ρ w`
  set z : ℂ := (ρ : ℂ) * w
  have hz : 0 < z.im := by simp [z]; positivity
  have hz0 : z ≠ 0 := mul_ne_zero (by exact_mod_cast hρ1.ne') hw0
  have hzk : z ^ k = ((ρ ^ k * ε : ℝ) : ℂ) * Complex.I := by
    simp only [z, mul_pow, hwk]; push_cast; ring
  have hc : (ρ ^ k * ε : ℝ) ≠ 0 := mul_ne_zero (pow_ne_zero _ hρ1.ne') hε0
  have hquot : aeval z N / aeval z Q = h z / (((ρ ^ k * ε : ℝ) : ℂ) * Complex.I) := by
    rw [hev, hevQ, ← hzk]
    simp only [h]
    field_simp
  have := him z hz
  rw [hquot] at this
  have him_eq : (h z / (((ρ ^ k * ε : ℝ) : ℂ) * Complex.I)).im = -(h z).re / (ρ ^ k * ε) := by
    set c : ℝ := ρ ^ k * ε
    rw [div_eq_mul_inv, mul_inv, Complex.inv_I]
    simp [Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.normSq_ofReal]
    field_simp
  rw [him_eq] at this
  have hρk : 0 < ρ ^ k := pow_pos hρ1 k
  have : -(h z).re / ε ≤ 0 := by
    have e : -(h z).re / (ρ ^ k * ε) = (-(h z).re / ε) / ρ ^ k := by
      field_simp
    rw [e] at this
    exact (div_nonpos_iff.mp this).elim (fun h => by linarith [h.2]) (fun h => h.1)
  exact absurd hρ (not_lt.mpr this)

end

end ArborealDecay.Separator
