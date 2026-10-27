import Spin2.Final.FinalAllX
import Spin2.Cont.ContWindow

/-!
# `cor:window` (a) for every `ℓ > 0` (A5')

`thm_cor_window_a` (`Spin2/Cont/ContWindow`) needs `ℓ < 1/(2L)` (so that `j_x ≤ N − 2`). With the top
coalescence scales (`FwAllBd`, `thm_multiscale_final_h0_allB`) the pair bound holds for every
`x ≠ 0` at `j = min(j_p, N − 2)`, and `|j − N| ≤ 2 + |log_L ℓ_N|` still gives `j/N → 1`, so
`β_ε^{-1}β_j → 1 − 3/(2πA)` as before (at `j = N − 2` this is `b_N/ǧ_{N−2} → 1 − 3/(2πA)`).

* `a5w_limitX`: `a5w_limit` with `|J_N − N| ≤ 2 + |log_L ℓ_N|`.
* `a5w_perNX`: `a5w_perN` for all `x ≠ 0`, at `j = min(j_p, N − 2)`.
* **`thm_cor_window_aX`**: `cor:window` (a) for every `ℓ > 0` (realisable: `ℓ ≤ √2/2`, since
  `|x| ≤ √2|x|_∞ ≤ L^N/√2`; `cx_ell_lt_one`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Filter Topology

/-- **`a5w_limit` with `|J_N − N| ≤ 2 + |log_L ℓ_N|`** in place of `J_N = ⌊N + log_L ℓ_N⌋` (pure). -/
theorem a5w_limitX (L : ℕ) (hL : 1 < (L : ℝ)) {A : ℝ} (hA : 3 / (2 * Real.pi) < A) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (ℓs : ℕ → ℝ) (hℓs : Tendsto ℓs atTop (𝓝 ℓ)) (P : ℕ → ℝ) (J : ℕ → ℕ)
    (G : ℕ → ℝ) (C₁ C₂ K : ℝ) (N₁ : ℕ)
    (h : ∀ N, N₁ ≤ N → |(J N : ℝ) - N| ≤ 2 + |Real.logb L (ℓs N)| ∧ 0 < G N ∧
      |1 / G N - A * (N * Real.log L) + J N * Step2.betaL L| ≤
        C₁ + C₂ * Real.log (A * (N * Real.log L)) ∧
      |P N - ((1 / G N) / (A * (N * Real.log L))) ^ (2 / 3 : ℝ)| ≤
        K * ((1 / G N) / (A * (N * Real.log L))) ^ (2 / 3 : ℝ) / (1 / G N)) :
    Tendsto P atTop (𝓝 ((1 - 3 / (2 * Real.pi * A)) ^ (2 / 3 : ℝ))) := by
  set lL := Real.log L with hlLd
  have hlL : 0 < lL := Real.log_pos hL
  have hπ : 0 < Real.pi := Real.pi_pos
  have hA0 : 0 < A := lt_trans (by positivity) hA
  have hAl : 0 < A * lL := mul_pos hA0 hlL
  -- `B_N → ∞`
  have hB : Tendsto (fun N : ℕ => A * (N * lL)) atTop atTop := by
    refine (tendsto_natCast_atTop_atTop.const_mul_atTop hAl).congr ?_
    intro N; ring
  -- `J_N / N → 1`
  have hlogb : Tendsto (fun N => Real.logb L (ℓs N)) atTop (𝓝 (Real.logb L ℓ)) := by
    simp only [Real.logb]; exact (hℓs.log hℓ.ne').div_const _
  have hJN0 : Tendsto (fun N : ℕ => ((J N : ℝ) - N) / N) atTop (𝓝 0) := by
    have hb := (tendsto_const_nhds (x := (2 : ℝ)).add hlogb.abs).div_atTop
      tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop 1] with N hN hN1
    obtain ⟨hJ, -⟩ := h N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have : |(J N : ℝ) - N| ≤ 2 + |Real.logb L (ℓs N)| := hJ
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hN0]
    exact div_le_div_of_nonneg_right this hN0.le
  have hJN : Tendsto (fun N : ℕ => (J N : ℝ) / N) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add hJN0
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    field_simp; ring
  -- the error of `λ_N = (1/G_N)/B_N`
  have he1 : Tendsto (fun N : ℕ => (C₁ + C₂ * Real.log (A * (N * lL))) / (A * (N * lL)))
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have := (tendsto_const_nhds (x := C₁)).div_atTop hB |>.add
      ((h2.comp hB).const_mul C₂)
    rw [mul_zero, add_zero] at this
    refine this.congr ?_
    intro N; simp only [Function.comp]; ring
  set lam := fun N : ℕ => (1 / G N) / (A * (N * lL)) with hlamd
  set c := 3 / (2 * Real.pi) / A with hcd
  have hμ : Tendsto (fun N : ℕ => 1 - (J N : ℝ) / N * c) atTop (𝓝 (1 - 1 * c)) :=
    tendsto_const_nhds.sub (hJN.mul_const c)
  have hlm : Tendsto (fun N : ℕ => lam N - (1 - (J N : ℝ) / N * c)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ he1
    filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop 1] with N hN hN1
    obtain ⟨-, hG, hX, -⟩ := h N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hBp : 0 < A * (N * lL) := by positivity
    have e : lam N - (1 - (J N : ℝ) / N * c) =
        (1 / G N - A * (N * lL) + J N * Step2.betaL L) / (A * (N * lL)) := by
      simp only [hlamd, hcd, Step2.betaL, ← hlLd]
      field_simp
      ring
    rw [Real.norm_eq_abs, e, abs_div, abs_of_pos hBp]
    exact div_le_div_of_nonneg_right hX hBp.le
  have hlam : Tendsto lam atTop (𝓝 (1 - 3 / (2 * Real.pi * A))) := by
    have := hμ.add hlm
    rw [add_zero] at this
    have e : 1 - 1 * c = 1 - 3 / (2 * Real.pi * A) := by
      simp only [hcd]; field_simp
    rw [e] at this
    refine this.congr ?_
    intro N; ring
  have hpos : 0 < 1 - 3 / (2 * Real.pi * A) := by
    have : 3 / (2 * Real.pi * A) < 1 := by
      rw [div_lt_one (by positivity)]
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).1 hA
      linarith
    linarith
  have hθ := hlam.rpow_const (p := (2 / 3 : ℝ)) (Or.inl hpos.ne')
  -- `G_N → 0`
  have hG : Tendsto G atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hB).div hlam hpos.ne'
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop 1] with N hN hN1
    obtain ⟨-, hG, -, -⟩ := h N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hBp : 0 < A * (N * lL) := by positivity
    simp only [hlamd, Pi.div_apply]
    field_simp
  have herr : Tendsto (fun N => K * lam N ^ (2 / 3 : ℝ) * G N) atTop (𝓝 0) := by
    have := (hθ.const_mul K).mul hG
    rwa [mul_zero] at this
  have hPθ : Tendsto (fun N => P N - lam N ^ (2 / 3 : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ herr
    filter_upwards [eventually_ge_atTop N₁] with N hN
    obtain ⟨-, hG, -, hP⟩ := h N hN
    rw [Real.norm_eq_abs]
    refine hP.trans (le_of_eq ?_)
    simp only [hlamd]
    field_simp
  have := hθ.add hPθ
  rw [add_zero] at this
  refine this.congr ?_
  intro N; ring


set_option maxHeartbeats 4000000 in
/-- **`a5w_perN` for all `x ≠ 0`**, at `j = min(j_p, N − 2)` (`FwAllBd`). Original: the per-`N` bounds of `cor:window` (a). For `A > 3/2π` and `N ≥ N₁`, at every `x ≠ 0` with
`j_x ≤ N − 2`, with `B = A N log L = β_N`: `j = j(|x|/L^N)`, `g = ǧ_j > 0` on the `h = 0`
trajectory from `b = 1/B`, `|1/g − B + jβ| ≤ C₁ + C₂ log B` and
`|P_B[0 ↔ x] − ((1/g)/B)^{2/3}| ≤ K((1/g)/B)^{2/3}/(1/g)`. -/
theorem a5w_perNX : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ K C₁ C₂ : ℝ,
    ∀ A : ℝ, 3 / (2 * Real.pi) < A → ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
    ∀ x : Lam 2 L N, x ≠ 0 →
    ∃ (jp j : ℕ) (g : ℝ), (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧ j = min jp (N - 2) ∧ 0 < g ∧
      |1 / g - A * (N * Real.log L) + j * betaL L| ≤
        C₁ + C₂ * Real.log (A * (N * Real.log L)) ∧
      |Pconn L N (A * (N * Real.log L)) x - ((1 / g) / (A * (N * Real.log L))) ^ (2 / 3 : ℝ)| ≤
        K * ((1 / g) / (A * (N * Real.log L))) ^ (2 / 3 : ℝ) / (1 / g) := by
  obtain ⟨L₀, hfa⟩ := thm_multiscale_final_h0_allB
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, g₀, K, N₀, hg₀, -, -, hF⟩ := hfa L hL
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
  obtain ⟨hℓ, hAc, -, hε, -, -, hcg, -, -, hKe, -, hCb, -⟩ := M.core.hC2
  have hBC := betaConcl_of hL2 M.core.hε1 M.core.hC2 M.core.hSp
  have hε1 := M.core.hε1
  set lL := Real.log L with hlLd
  have hlL : 0 < lL := Real.log_pos (by linarith)
  set β := betaL L with hβd
  have hβ : 0 < β := by rw [hβd, betaL]; positivity
  set cg := M.core.cg
  set eR := eRange β M.core.Ke 1 with heRd
  have heR : 0 ≤ eR := by rw [heRd, eRange]; positivity
  have hCgu : 0 ≤ Cgu β cg := by unfold Cgu; positivity
  set C₁ := 2 * (1 + β) * eR + Cgu β cg * |betaAsymK β cg eR| with hC₁d
  set C₂ := Cgu β cg * (1 / β) with hC₂d
  refine ⟨K, C₁, C₂, fun A hA => ?_⟩
  set E := betaShE L cg M.core.Ke M.core.Cb with hEd
  set a := betaShA L cg with had
  have hE : 0 ≤ E := by
    rw [hEd, betaShE, betaLogE]
    have : 0 ≤ Cgu (betaL L) cg := hCgu
    positivity
  have ha : 0 ≤ a := by rw [had, betaShA]; exact div_nonneg hCgu hβ.le
  set c' := E + a * |Real.log (2 * a)| with hc'd
  have hc' : 0 ≤ c' := by positivity
  have hπ : 0 < Real.pi := Real.pi_pos
  have hA0 : 0 < A := lt_trans (by positivity) hA
  set δ := A * lL - β with hδd
  have hδ : 0 < δ := by
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).1 hA
    have e : β = 3 / (2 * Real.pi) * lL := by rw [hβd, betaL, ← hlLd]; ring
    have : 3 / (2 * Real.pi) * lL < A * lL := mul_lt_mul_of_pos_right hA hlL
    rw [hδd, e]; linarith
  set f := fun N : ℕ => A * (N * lL) - ((N - 2 : ℕ) : ℝ) * β with hfd
  have hfδ : ∀ N : ℕ, 2 ≤ N → δ * N ≤ f N := by
    intro N hN
    simp only [hfd, hδd]
    push_cast [Nat.cast_sub hN]
    nlinarith
  have hfT : Tendsto f atTop atTop :=
    tendsto_atTop_mono' _ (by filter_upwards [eventually_ge_atTop 2] with N hN using hfδ N hN)
      (tendsto_natCast_atTop_atTop.const_mul_atTop hδ)
  set errB := fun N : ℕ => E + a * Real.log (2 * (2 * (A * (N * lL)) + c')) with herrBd
  have herrT : Tendsto (fun N : ℕ => errB N / N) atTop (𝓝 0) := by
    have h1 := a5w_log_div (α := 4 * A * lL) (by positivity) (2 * c')
    have h2 := ((tendsto_const_nhds (x := E)).div_atTop tendsto_natCast_atTop_atTop).add
      (h1.const_mul a)
    rw [mul_zero, add_zero] at h2
    refine h2.congr ?_
    intro N
    simp only [herrBd]
    ring_nf
  have hev : ∀ᶠ N : ℕ in atTop, max N₀ 3 ≤ N ∧ 4 / M.core.ε ≤ f N ∧ 1 / g₀ ≤ f N ∧
      errB N / N < δ / 4 :=
    (eventually_ge_atTop _).and ((hfT.eventually_ge_atTop _).and
      ((hfT.eventually_ge_atTop _).and (herrT.eventually_lt_const (by linarith))))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  refine ⟨N₁, fun N hN x hx => ?_⟩
  obtain ⟨hNm, hf4, hfg, herr⟩ := hN₁ N hN
  have hN0 : N₀ ≤ N := le_of_max_le_left hNm
  have hN3 : 3 ≤ N := le_of_max_le_right hNm
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set B := A * (N * lL) with hBd
  have hB : 0 < B := by positivity
  set βR := f N with hβRd
  have hβR : 0 < βR := lt_of_lt_of_le (by positivity) hf4
  have hβRB : βR + ((N - 2 : ℕ) : ℝ) * β = B := by simp only [hβRd, hfd]; ring
  have hNhβ : 0 ≤ ((N - 2 : ℕ) : ℝ) * β := by positivity
  have herr' : errB N < βR / 4 := by
    have := (div_lt_iff₀ hNr).1 herr
    have := hfδ N (by omega)
    linarith
  have hβR4 : 4 ≤ βR := by
    have : 4 ≤ 4 / M.core.ε := by rw [le_div_iff₀ hε]; linarith
    linarith
  set b := 1 / B with hbd
  have hbB : 1 / b = B := by rw [hbd, one_div_one_div]
  set m := 1 / (4 * βR * (L : ℝ) ^ (2 * N)) with hmd
  have hLN : (0 : ℝ) < (L : ℝ) ^ (2 * N) := by positivity
  have hm : 0 < m := by positivity
  have h4m : 4 * (m * (L : ℝ) ^ (2 * N)) = 1 / βR := by
    rw [hmd]; field_simp
  have hmR : m ∈ Step2.mRange L N := by
    refine fin_mRange hL2 (by omega) hm ?_
    have : m * (L : ℝ) ^ (2 * N) = 1 / (4 * βR) := by
      rw [hmd]; field_simp
    rw [this, div_le_one (by positivity)]; linarith
  have hg1 : 1 / βR ≤ g₀ := by
    rw [div_le_iff₀ hβR]
    have := (div_le_iff₀ hg₀).1 hfg
    linarith
  haveI : Fact (0 < (a5wR M N).ℓ) := ⟨hℓ⟩
  haveI : Fact (0 < (a5wR M N).A) := ⟨hAc⟩
  set R := a5wR M N with hRd
  obtain ⟨-, -, hall, -⟩ := hF N R rfl rfl rfl rfl rfl hN0 m βR hm hβR h4m.le hg1
  obtain ⟨hBC1, -, -⟩ := hBC N R rfl rfl rfl rfl rfl (by omega) (N - 2) (by omega) m hmR
  have h2ε : ∀ β' : ℝ, βR / 2 ≤ β' → 2 / M.core.ε ≤ β' := by
    intro β' h
    have : 2 / M.core.ε = 4 / M.core.ε / 2 := by ring
    linarith
  obtain ⟨-, -, -, -, -, -, hlo, -⟩ := hBC1 (2 * βR) (h2ε _ (by linarith))
  obtain ⟨-, -, -, -, -, -, hhi, -⟩ := hBC1 (βR / 2) (h2ε _ le_rfl)
  -- the logarithmic errors are at most `errB N`
  have hlog : ∀ β' : ℝ, 0 < β' → β' + ((N - 2 : ℕ) : ℝ) * β ≤ 2 * B →
      E + a * Real.log (2 * (β' + ((N - 2 : ℕ) : ℝ) * β + E + a * |Real.log (2 * a)|)) ≤
        errB N := by
    intro β' hβ' hle
    simp only [herrBd]
    have h0 : 0 < 2 * (β' + ((N - 2 : ℕ) : ℝ) * β + E + a * |Real.log (2 * a)|) := by positivity
    have hle2 : 2 * (β' + ((N - 2 : ℕ) : ℝ) * β + E + a * |Real.log (2 * a)|) ≤
        2 * (2 * B + c') := by linarith [hc'd]
    have := Real.log_le_log h0 hle2
    have := mul_le_mul_of_nonneg_left this ha
    linarith
  have elo := hlog (2 * βR) (by positivity) (by linarith)
  have ehi := hlog (βR / 2) (by positivity) (by linarith)
  have hlo' := abs_le.1 (hlo.trans elo)
  have hhi' := abs_le.1 (hhi.trans ehi)
  set blo := bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (1 / (2 * βR))
  set bhi := bFin R M.core.κ M.core.cm M.core.cT (N - 2) M.core.ε m (1 / (βR / 2))
  have hblo : blo ≤ b := by
    have h1 : B ≤ 1 / blo := by linarith
    have := one_div_le_one_div_of_le hB h1
    rwa [one_div_one_div] at this
  have hbhi : b ≤ bhi := by
    have h0 : 0 < 1 / bhi := by linarith
    have h1 : 1 / bhi ≤ B := by linarith
    have := one_div_le_one_div_of_le h0 h1
    rwa [one_div_one_div] at this
  have e₂ : (2 : ℝ) / βR = 1 / (βR / 2) := by field_simp
  obtain ⟨-, hD, hPair, -⟩ := hall b (by rw [ctBracket, e₂]; exact ⟨hblo, hbhi⟩)
  obtain ⟨jp, hjp, -, -, hPb⟩ := hPair x hx
  set j := min jp (N - 2) with hjd
  have hjN : j ≤ N - 2 := min_le_right _ _
  have hBA := (M.spinD N R rfl rfl rfl rfl rfl (by omega) (N - 2) (by omega)).2.2.1 m hmR b
    (b - m) hD j hjN
  obtain ⟨hg0, hgε, -⟩ := hD j hjN
  set g := (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 with hgd
  have hg1 : g ≤ 1 := hgε.trans hε1
  refine ⟨jp, j, g, hjp, rfl, hg0, ?_, ?_⟩
  · rw [hbB] at hBA
    have hgb : Real.log (g / b) ≤ Real.log B := by
      refine Real.log_le_log (div_pos hg0 (by positivity)) ?_
      rw [div_eq_mul_one_div, hbB]
      nlinarith
    have k1 := mul_le_mul_of_nonneg_left hgb (show 0 ≤ Cgu β cg * (1 / β) by positivity)
    have k2 : betaAsymK β cg eR * g ≤ |betaAsymK β cg eR| := by
      calc betaAsymK β cg eR * g ≤ |betaAsymK β cg eR| * g :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hg0.le
        _ ≤ |betaAsymK β cg eR| * 1 := mul_le_mul_of_nonneg_left hg1 (abs_nonneg _)
        _ = _ := mul_one _
    have k3 := mul_le_mul_of_nonneg_left k2 hCgu
    refine hBA.trans ?_
    rw [hC₁d, hC₂d]
    nlinarith
  · simp only [thetaSq, betaJ, hbB] at hPb
    exact hPb

set_option maxHeartbeats 1000000 in
/-- **`cor:window` (a) for every `ℓ > 0`.** For `L ≥ L₀`, `A > 3/2π` and points `x_N ∈ Λ_N`
with `|x_N|/L^N → ℓ > 0`: `P_{A log L^N}[0 ↔ x_N] → (1 − 3/(2πA))^{2/3}` as `N → ∞`. -/
theorem thm_cor_window_aX : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ A : ℝ, 3 / (2 * Real.pi) < A →
    ∀ (x : ∀ N : ℕ, Lam 2 L N) (ℓ : ℝ), 0 < ℓ →
      Tendsto (fun N => eucl (x N) / (L : ℝ) ^ N) atTop (𝓝 ℓ) →
      Tendsto (fun N => Pconn L N (A * Real.log ((L : ℝ) ^ N)) (x N)) atTop
        (𝓝 ((1 - 3 / (2 * Real.pi * A)) ^ (2 / 3 : ℝ))) := by
  obtain ⟨L₀, hP⟩ := a5w_perNX
  refine ⟨max L₀ 2, fun L _ hL A hA x ℓ hℓ hℓs => ?_⟩
  obtain ⟨K, C₁, C₂, hA'⟩ := hP L (le_of_max_le_left hL)
  obtain ⟨N₁, hN₁⟩ := hA' A hA
  have hL2 : 2 ≤ L := le_of_max_le_right hL
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL2
  have hL0 : (0 : ℝ) < L := by linarith
  set ℓs := fun N => eucl (x N) / (L : ℝ) ^ N with hℓsd
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hℓs.eventually_const_lt hℓ)
  set N₃ := max (max N₁ N₂) 2
  have hch : ∀ N : ℕ, ∃ (j : ℕ) (g : ℝ), N₃ ≤ N →
      |(j : ℝ) - N| ≤ 2 + |Real.logb L (ℓs N)| ∧ 0 < g ∧
      |1 / g - A * (N * Real.log L) + j * betaL L| ≤
        C₁ + C₂ * Real.log (A * (N * Real.log L)) ∧
      |Pconn L N (A * (N * Real.log L)) (x N) - ((1 / g) / (A * (N * Real.log L))) ^ (2 / 3 : ℝ)| ≤
        K * ((1 / g) / (A * (N * Real.log L))) ^ (2 / 3 : ℝ) / (1 / g) := by
    intro N
    by_cases hN : N₃ ≤ N
    swap
    · exact ⟨0, 0, fun h => absurd h hN⟩
    have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hN2' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
    have hpos := hN₂ N hN2'
    have hLN : (0 : ℝ) < (L : ℝ) ^ N := by positivity
    have he : 0 < eucl (x N) := (div_pos_iff_of_pos_right hLN).1 hpos
    have hx : x N ≠ 0 := by
      intro h0
      have := eucl_le_two_supNorm (x N)
      rw [h0, (FRD.supNorm_eq_zero_iff _).2 rfl] at this
      rw [h0] at he
      push_cast at this
      linarith
    obtain ⟨jp, j, g, hjp, hj, hg, h3, h4⟩ := hN₁ N hN1 (x N) hx
    refine ⟨j, g, fun _ => ⟨?_, hg, h3, h4⟩⟩
    have hjp' : (jp : ℤ) = ⌊(N : ℝ) + Real.logb L (ℓs N)⌋ := hjp
    have f1 := Int.floor_le ((N : ℝ) + Real.logb L (ℓs N))
    have f2 := Int.lt_floor_add_one ((N : ℝ) + Real.logb L (ℓs N))
    rw [← hjp'] at f1 f2
    push_cast at f1 f2
    have t1 := neg_abs_le (Real.logb L (ℓs N))
    have t2 := le_abs_self (Real.logb L (ℓs N))
    rcases le_total jp (N - 2) with h | h
    · rw [hj, min_eq_left h, abs_le]
      constructor <;> linarith
    · rw [hj, min_eq_right h, Nat.cast_sub hN2, abs_le]
      push_cast
      constructor <;> linarith [abs_nonneg (Real.logb L (ℓs N))]
  choose J G hJG using hch
  refine (a5w_limitX L hL1 hA hℓ ℓs hℓs (fun N => Pconn L N (A * (N * Real.log L)) (x N)) J G
    C₁ C₂ K N₃ hJG).congr ?_
  intro N
  simp only [Real.log_pow]

end

end Spin2
