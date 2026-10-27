import Spin2.Case2.Case2Loop
import PtCorr2.Obs.ObsHistRelW
import Obs2.Flow.Tau2Bd

/-!
# `Case2Bulk` (i), (iii) and the bound on `q = ν♭S` along a regular history

A bundle `C2Ctx R N_h t c_μ c_z c_d c` of bulk bounds along a history (`ValidAt` below `N_h`,
`0 < ǧ_j ≤ 1` nondecreasing, `|μ_j| ≤ c_μǧ_j`, `|ζ_j| ≤ 2c_zǧ_j`, the rescaled increments
`|g_{i+1} - g_i| ≤ c_dǧ_i²|Z_{i+1}|²`, `m²L^{2(N_h+1)} ≤ 1`) with one constant `c` bounding
`ℓ⁴, ℓ²c_μ, c_z, ℓ²c_z, c_d`. Every covariance `C_i` is used at its own Gram scale
`ℓ_i² = ℓ²/(16|Z_{i+1}|)`; the factors `|Z|` cancel against the weights of the couplings
(`|Z_m|/|Z_l| ≤ (8/7)^{|m-l|}`).

* `gdiff`: `|g_k - g_i| ≤ c_dǧ_k²(k-i)(8/7)^{k-i}|Z_{i+1}||Z_{k+1}|`;
* **`drift_le`** (`Case2Bulk` (iii)): `|4δ_k∑_{i<k}(g_k-g_i)rowS_{C_i}| + |∑_{i<k}(g_k-g_i)𝔩_{C_i,C_k}|
  ≤ (9/64)c²ǧ_k²`;
* **`q_le`**: `|ν♭_kS_k| ≤ 7cǧ_k` (`k ≤ N_h`);
* `bubble_eq` (exact, `R.P = Pc`): `g_k(𝔩_{w_{k+1}} - 𝔩_{w_k}) = ǧ_k/(1+n_k) · (𝔩(w'_k + C'_{k+1}) - 𝔩(w'_k))`
  with the dressed `w'_k = Z_{k+1}∑_{i<k}Γ^int_i`, `C'_{k+1} = Z_{k+1}Γ^int_k` of `DressedFRD`
  (`Obs2.lfunC_kmat`);
* `LcProp`, `lcProp_of`: the third line of `Step2.D2.prop_d2_lines12` as a named property of
  `(ζ̄, K, c_S)`;
* **`bubble_le`** (`Case2Bulk` (i)): `|g_k(𝔩_{w_{k+1}} - 𝔩_{w_k}) - (β/3)ǧ_k| ≤ B₁(ǧ_k² + ǧ_kzA_k)`,
  `B₁ = bubB L c K c_S`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2

/-! ### Pure helpers -/

theorem natCast_le_two_pow (m : ℕ) : (m : ℝ) ≤ 2 ^ m := by
  exact_mod_cast (Nat.lt_two_pow_self (n := m)).le

theorem m_geom_le {x : ℝ} (hx : 0 ≤ x) (m : ℕ) : (m : ℝ) * x ^ m ≤ (2 * x) ^ m := by
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (natCast_le_two_pow m) (pow_nonneg hx _)

theorem pow_ratio_L {L : ℝ} (hL : 0 < L) {i k : ℕ} (hik : i ≤ k) :
    L ^ (i + 1) / L ^ (k + 1) = (L⁻¹) ^ (k - i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hik
  rw [Nat.add_sub_cancel_left, show L ^ (i + m + 1) = L ^ (i + 1) * L ^ m by
    rw [← pow_add]; congr 1; omega, div_mul_eq_div_div, div_self (by positivity), one_div, inv_pow]

theorem pow_ratio_L2 {L : ℝ} (hL : 0 < L) {i k : ℕ} (hik : i ≤ k) :
    (L ^ (i + 1)) ^ 2 / (L ^ (k + 1)) ^ 2 = ((L ^ 2)⁻¹) ^ (k - i) := by
  rw [← div_pow, pow_ratio_L hL hik, ← pow_mul, mul_comm, pow_mul, inv_pow]

theorem norm_gr_sub_le {g : ℝ} (hg : 0 ≤ g) {n : ℂ} (hn : ‖n‖ ≤ 1 / 8) :
    ‖(g : ℂ) / (1 + n) - (g : ℂ)‖ ≤ 8 / 7 * g * ‖n‖ := by
  have h1n : 7 / 8 ≤ ‖1 + n‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-n)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this; linarith
  have hne : (1 + n) ≠ 0 := norm_ne_zero_iff.1 (by linarith)
  have e : (g : ℂ) / (1 + n) - (g : ℂ) = -((g : ℂ) * n / (1 + n)) := by
    field_simp; ring
  rw [e, norm_neg, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg,
    div_le_iff₀ (by linarith)]
  have : 0 ≤ g * ‖n‖ := by positivity
  nlinarith

/-! ### The bulk context -/

variable {L N : ℕ} [NeZero L]

section Ctx

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The bulk bounds along a history** used for `Case2Bulk`. -/
structure C2Ctx (Nh : ℕ) (t : Hist.Seq (Xs R)) (cmu' cz' cd c : ℝ) : Prop where
  hN : Nh + 2 ≤ N
  hL7 : 7 ≤ L
  hρ0 : 0 ≤ R.ρ
  hρ8 : R.ρ ≤ 1 / 8
  hV : ∀ j < Nh, ValidAt R j
  hVL : ValidAtL R Nh
  hg : ∀ j ≤ Nh, 0 < (t j).1 ∧ (t j).1 ≤ 1
  hgm : ∀ j < Nh, (t j).1 ≤ (t (j + 1)).1
  hg2 : ∀ j < Nh, (t (j + 1)).1 ≤ 2 * (t j).1
  hμ : ∀ j ≤ Nh, |(t j).2.1| ≤ cmu' * (t j).1
  hζ : ∀ j ≤ Nh, ‖zetaH R j t‖ ≤ 2 * cz' * (t j).1
  hdg : ∀ i < Nh, ‖Obs2.gH R t (i + 1) - Obs2.gH R t i‖ ≤ cd * (t i).1 ^ 2 * zH R t (i + 1) ^ 2
  hZw : ∀ j < Nh, ‖stZ' R (rawHist R j t) * (rawHist R j t).w1‖ ≤ R.ℓ ^ 2 * ((L : ℝ) ^ j) ^ 2
  hm0 : 0 ≤ R.msq
  hm : R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1
  hcmu : 0 ≤ cmu'
  hcz : 0 ≤ cz'
  hcd : 0 ≤ cd
  hc4 : R.ℓ ^ 4 ≤ c
  hcm : R.ℓ ^ 2 * cmu' ≤ c
  hcz1 : cz' ≤ c
  hcz2 : R.ℓ ^ 2 * cz' ≤ c
  hcd1 : cd ≤ c

end Ctx

namespace C2Ctx

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} {t : Hist.Seq (Xs R)}
  {cmu' cz' cd c : ℝ} (X : C2Ctx R Nh t cmu' cz' cd c)
include X

theorem c_nonneg : 0 ≤ c := (le_trans (by positivity) X.hc4)

theorem L_pos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)

theorem L7 : (7 : ℝ) ≤ L := by exact_mod_cast X.hL7

theorem gmono {l k : ℕ} (hlk : l ≤ k) (hk : k ≤ Nh) : (t l).1 ≤ (t k).1 := by
  induction k, hlk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hlk ih => exact (ih (by omega)).trans (X.hgm k (by omega))

theorem zpos (i : ℕ) : 0 < zH R t i := zH_pos R X.hρ0 X.hρ8 t i

/-- `C_i` at its own Gram scale `ℓ_i² = ℓ²/(16|Z_{i+1}|)`. -/
theorem cov {i : ℕ} (hi : i < Nh) :
    GoodCov2 i (fscale (stZ' R (rawHist R i t)) * R.ℓ / 4) (Obs2.histCovO R t i) ∧
      TInv (Obs2.histCovO R t i) ∧ CSym (Obs2.histCovO R t i) ∧
      ∀ x y, Obs2.histCovO R t i x y = Obs2.histCovO R t i y x :=
  histCovO_props_i R X.hV X.hVL t hi.le

theorem iN {i : ℕ} (hi : i < Nh) : i + 1 < N := by have := X.hN; omega

/-- `|δ_k| ≤ ℓ²/(32|Z_{k+1}|L^{2(k+1)})`. -/
theorem dl_le {k : ℕ} (hk : k < Nh) :
    ‖Obs2.dlH R t k‖ ≤ R.ℓ ^ 2 / (16 * zH R t (k + 1)) / (2 * ((L : ℝ) ^ (k + 1)) ^ 2) := by
  obtain ⟨hC, -⟩ := X.cov hk
  obtain ⟨hc, hδ, hδ'⟩ := Obs2.histCov_consts R t X.hV hk
  have h := (cov_c0_delta_le hC hc hδ hδ').2
  rwa [ellI_sq] at h

theorem rowS_le {i : ℕ} (hi : i < Nh) (a : Lam 2 L N) :
    ‖Obs2.rowS (Obs2.histCovO R t i) a‖ ≤
      18 * ((L : ℝ) ^ (i + 1)) ^ 2 * (R.ℓ ^ 2 / (16 * zH R t (i + 1))) := by
  have h := Obs2.norm_rowS_le (X.cov hi).1 (X.iN hi) a
  rwa [ellI_sq] at h

theorem lfunX_le {i k : ℕ} (hi : i < Nh) (hk : k < Nh) (a : Lam 2 L N) :
    ‖Obs2.lfunX (Obs2.histCovO R t i) (Obs2.histCovO R t k) a‖ ≤
      36 * (R.ℓ ^ 2 / (16 * zH R t (i + 1))) * (R.ℓ ^ 2 / (16 * zH R t (k + 1))) *
        ((L : ℝ) ^ (i + 1) / (L : ℝ) ^ (k + 1)) := by
  have h := Obs2.norm_lfunX_le (X.cov hi).1 (X.iN hi) (X.cov hk).1 a
  rwa [ellI_sq, ellI_sq] at h

/-- The telescoped increment of `g`. -/
theorem gdiff {i k : ℕ} (hik : i ≤ k) (hk : k ≤ Nh) :
    ‖Obs2.gH R t k - Obs2.gH R t i‖ ≤
      cd * (t k).1 ^ 2 * ((k - i : ℕ) : ℝ) * (8 / 7 : ℝ) ^ (k - i) *
        (zH R t (i + 1) * zH R t (k + 1)) := by
  -- telescoping
  have htel : ∀ k', i ≤ k' → ‖Obs2.gH R t k' - Obs2.gH R t i‖ ≤
      ∑ l ∈ Ico i k', ‖Obs2.gH R t (l + 1) - Obs2.gH R t l‖ := by
    intro k' hk'
    induction k', hk' using Nat.le_induction with
    | base => simp
    | succ k' hk' ih =>
      rw [sum_Ico_succ_top hk']
      have e : Obs2.gH R t (k' + 1) - Obs2.gH R t i =
          (Obs2.gH R t k' - Obs2.gH R t i) + (Obs2.gH R t (k' + 1) - Obs2.gH R t k') := by ring
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add ih le_rfl)
  refine (htel k hik).trans ?_
  set M := cd * (t k).1 ^ 2 * (8 / 7 : ℝ) ^ (k - i) * (zH R t (i + 1) * zH R t (k + 1)) with hM
  have hterm : ∀ l ∈ Ico i k, ‖Obs2.gH R t (l + 1) - Obs2.gH R t l‖ ≤ M := by
    intro l hl
    have hl' := mem_Ico.1 hl
    refine (X.hdg l (by omega)).trans ?_
    have hgl := (X.hg l (by omega)).1.le
    have hgg : (t l).1 ^ 2 ≤ (t k).1 ^ 2 :=
      pow_le_pow_left₀ hgl (X.gmono hl'.2.le hk) 2
    have h1 := zH_ratio_up R X.hρ0 X.hρ8 t (show i + 1 ≤ l + 1 by omega)
    have h2 := zH_ratio_down R X.hρ0 X.hρ8 t (show l + 1 ≤ k + 1 by omega)
    have hz := X.zpos (l + 1)
    have hpow : (8 / 7 : ℝ) ^ (l + 1 - (i + 1)) * (8 / 7 : ℝ) ^ (k + 1 - (l + 1)) =
        (8 / 7 : ℝ) ^ (k - i) := by rw [← pow_add]; congr 1; omega
    have hzz : zH R t (l + 1) ^ 2 ≤ (8 / 7 : ℝ) ^ (k - i) * (zH R t (i + 1) * zH R t (k + 1)) := by
      rw [sq, ← hpow]
      have := mul_le_mul h1 h2 hz.le (by positivity)
      linarith
    rw [hM]
    have hcd := X.hcd
    calc cd * (t l).1 ^ 2 * zH R t (l + 1) ^ 2
        ≤ cd * (t k).1 ^ 2 * ((8 / 7 : ℝ) ^ (k - i) * (zH R t (i + 1) * zH R t (k + 1))) := by
          gcongr
      _ = _ := by ring
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul, hM]
  ring

/-- **`Case2Bulk` (iii)**: the drift terms. -/
theorem drift_le {k : ℕ} (hk : k < Nh) (a : Lam 2 L N) :
    ‖4 * Obs2.dlH R t k * ∑ i ∈ range k,
        (Obs2.gH R t k - Obs2.gH R t i) * Obs2.rowS (Obs2.histCovO R t i) a‖ +
      ‖∑ i ∈ range k, (Obs2.gH R t k - Obs2.gH R t i) *
        Obs2.lfunX (Obs2.histCovO R t i) (Obs2.histCovO R t k) a‖ ≤
      9 / 64 * c ^ 2 * (t k).1 ^ 2 := by
  have hL0 := X.L_pos
  have hL7 := X.L7
  have hℓ : 0 < R.ℓ := Fact.out
  set g := (t k).1
  have hg0 : 0 ≤ g := (X.hg k hk.le).1.le
  set K0 := 9 / 64 * R.ℓ ^ 4 * cd * g ^ 2 with hK0
  have hK0n : 0 ≤ K0 := by have := X.hcd; positivity
  have hzk := X.zpos (k + 1)
  -- the drift of the tadpole part
  set y := 16 / 7 * ((L : ℝ) ^ 2)⁻¹ with hy
  have hy0 : 0 ≤ y := by positivity
  have hy3 : y ≤ 1 / 3 := by
    rw [hy, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith
  have hdr : ‖4 * Obs2.dlH R t k * ∑ i ∈ range k,
      (Obs2.gH R t k - Obs2.gH R t i) * Obs2.rowS (Obs2.histCovO R t i) a‖ ≤ K0 * (1 / 2) := by
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
    rw [mul_sum]
    refine (sum_le_sum fun i hi => ?_).trans ((mul_sum _ _ _).symm.le.trans
      (mul_le_mul_of_nonneg_left (Obs2.geom_tail_le hy0 hy3 k) hK0n))
    have hi' := mem_range.1 hi
    have hzi := X.zpos (i + 1)
    have h1 := X.dl_le hk
    have h2 := X.gdiff hi'.le hk.le
    have h3 := X.rowS_le (hi'.trans hk) a
    rw [norm_mul]
    have e4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [e4, norm_mul (Obs2.gH R t k - Obs2.gH R t i)]
    have hb : 4 * ‖Obs2.dlH R t k‖ * (‖Obs2.gH R t k - Obs2.gH R t i‖ *
        ‖Obs2.rowS (Obs2.histCovO R t i) a‖) ≤
        4 * (R.ℓ ^ 2 / (16 * zH R t (k + 1)) / (2 * ((L : ℝ) ^ (k + 1)) ^ 2)) *
          (cd * g ^ 2 * ((k - i : ℕ) : ℝ) * (8 / 7 : ℝ) ^ (k - i) *
            (zH R t (i + 1) * zH R t (k + 1)) *
          (18 * ((L : ℝ) ^ (i + 1)) ^ 2 * (R.ℓ ^ 2 / (16 * zH R t (i + 1))))) := by
      have := X.hcd
      gcongr
    refine hb.trans ?_
    have hr := pow_ratio_L2 hL0 hi'.le
    have e : 4 * (R.ℓ ^ 2 / (16 * zH R t (k + 1)) / (2 * ((L : ℝ) ^ (k + 1)) ^ 2)) *
          (cd * g ^ 2 * ((k - i : ℕ) : ℝ) * (8 / 7 : ℝ) ^ (k - i) *
            (zH R t (i + 1) * zH R t (k + 1)) *
          (18 * ((L : ℝ) ^ (i + 1)) ^ 2 * (R.ℓ ^ 2 / (16 * zH R t (i + 1))))) =
        K0 * (((k - i : ℕ) : ℝ) * ((8 / 7 : ℝ) * ((L : ℝ) ^ 2)⁻¹) ^ (k - i)) := by
      rw [hK0, mul_pow, ← hr]
      field_simp
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hK0n
    refine (m_geom_le (by positivity) _).trans (le_of_eq ?_)
    rw [hy]; ring_nf
  -- the drift of the bubble part
  set y' := 16 / 7 * (L : ℝ)⁻¹ with hy'
  have hy'0 : 0 ≤ y' := by positivity
  have hy'3 : y' ≤ 1 / 3 := by
    rw [hy', ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  have hdx : ‖∑ i ∈ range k, (Obs2.gH R t k - Obs2.gH R t i) *
      Obs2.lfunX (Obs2.histCovO R t i) (Obs2.histCovO R t k) a‖ ≤ K0 * (1 / 2) := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum fun i hi => ?_).trans ((mul_sum _ _ _).symm.le.trans
      (mul_le_mul_of_nonneg_left (Obs2.geom_tail_le hy'0 hy'3 k) hK0n))
    have hi' := mem_range.1 hi
    have hzi := X.zpos (i + 1)
    have h2 := X.gdiff hi'.le hk.le
    have h3 := X.lfunX_le (hi'.trans hk) hk a
    rw [norm_mul]
    have hb := mul_le_mul h2 h3 (norm_nonneg _) (by have := X.hcd; positivity)
    refine hb.trans ?_
    have hr := pow_ratio_L hL0 hi'.le
    have e : cd * g ^ 2 * ((k - i : ℕ) : ℝ) * (8 / 7 : ℝ) ^ (k - i) *
          (zH R t (i + 1) * zH R t (k + 1)) *
        (36 * (R.ℓ ^ 2 / (16 * zH R t (i + 1))) * (R.ℓ ^ 2 / (16 * zH R t (k + 1))) *
          ((L : ℝ) ^ (i + 1) / (L : ℝ) ^ (k + 1))) =
        K0 * (((k - i : ℕ) : ℝ) * ((8 / 7 : ℝ) * (L : ℝ)⁻¹) ^ (k - i)) := by
      rw [hK0, mul_pow, hr]
      field_simp
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hK0n
    refine (m_geom_le (by positivity) _).trans (le_of_eq ?_)
    rw [hy']; ring_nf
  have hfin : K0 * (1 / 2) + K0 * (1 / 2) ≤ 9 / 64 * c ^ 2 * g ^ 2 := by
    have h4 := X.hc4
    have hd := X.hcd1
    have hcd0 := X.hcd
    have : R.ℓ ^ 4 * cd ≤ c * c := mul_le_mul h4 hd hcd0 X.c_nonneg
    rw [hK0]
    have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
    nlinarith
  linarith

/-- **The bound on `q_k = ν♭_kS_k`** (`k ≤ N_h`). -/
theorem q_le {k : ℕ} (hk : k ≤ Nh) (a : Lam 2 L N) :
    ‖Obs2.nuFH R t k * ∑ i ∈ range k, Obs2.rowS (Obs2.histCovO R t i) a‖ ≤ 7 * c * (t k).1 := by
  have hL0 := X.L_pos
  have hL7 := X.L7
  have hℓ : 0 < R.ℓ := Fact.out
  set g := (t k).1
  have hg0 : 0 ≤ g := (X.hg k hk).1.le
  have hc0 := X.c_nonneg
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp only [range_zero, sum_empty, mul_zero, norm_zero]; positivity
  set zp := zH R t (k + 1)
  have hzp := X.zpos (k + 1)
  -- `ν♭_k`
  have hmk : R.msq * ((L : ℝ) ^ k) ^ 2 ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ X.hm0) X.hm
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega)) 2
  set Q := cmu' * g + 8 / 7 * (2 * cz' * g) with hQ
  have hnu : ‖Obs2.nuFH R t k‖ ≤ zp / ((L : ℝ) ^ k) ^ 2 * Q := by
    unfold Obs2.nuFH
    refine (norm_sub_le _ _).trans ?_
    have hNu : ‖stNu R k (rawHist R k t) (t k).2.1‖ = |(t k).2.1| * zp / ((L : ℝ) ^ k) ^ 2 := by
      unfold stNu
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_natCast,
        show (L : ℝ) ^ (2 * k) = ((L : ℝ) ^ k) ^ 2 by ring]
      rfl
    have hZr : zH R t k ≤ 8 / 7 * zp := by
      have := zH_ratio_down R X.hρ0 X.hρ8 t (show k ≤ k + 1 by omega)
      rwa [show k + 1 - k = 1 by omega, pow_one] at this
    have hA : ‖stA R (rawHist R k t) * (R.msq : ℂ)‖ ≤ 8 / 7 * zp * ‖zetaH R k t‖ * R.msq := by
      unfold stA
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg X.hm0]
      have e : stZeta R (rawHist R k t) = zetaH R k t := rfl
      rw [e]
      have := norm_nonneg (zetaH R k t)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hZr (norm_nonneg _)) X.hm0
    rw [hNu]
    refine (add_le_add le_rfl hA).trans ?_
    have hμ := X.hμ k hk
    have hζ := X.hζ k hk
    have hLk : 0 < ((L : ℝ) ^ k) ^ 2 := by positivity
    have e1 : 8 / 7 * zp * ‖zetaH R k t‖ * R.msq =
        zp / ((L : ℝ) ^ k) ^ 2 * (8 / 7 * ‖zetaH R k t‖ * (R.msq * ((L : ℝ) ^ k) ^ 2)) := by
      field_simp
    have e2 : |(t k).2.1| * zp / ((L : ℝ) ^ k) ^ 2 = zp / ((L : ℝ) ^ k) ^ 2 * |(t k).2.1| := by ring
    rw [e1, e2, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hQ]
    have hm0' : 0 ≤ R.msq * ((L : ℝ) ^ k) ^ 2 := mul_nonneg X.hm0 (by positivity)
    have : 8 / 7 * ‖zetaH R k t‖ * (R.msq * ((L : ℝ) ^ k) ^ 2) ≤ 8 / 7 * (2 * cz' * g) * 1 := by
      have := X.hcz
      gcongr
    linarith
  -- `S_k`
  set y := 8 / 7 * ((L : ℝ) ^ 2)⁻¹ with hy
  have hy0 : 0 ≤ y := by positivity
  have hy3 : y ≤ 1 / 3 := by
    rw [hy, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith
  have hQ0 : 0 ≤ Q := by have := X.hcmu; have := X.hcz; positivity
  set K1 := 9 / 8 * R.ℓ ^ 2 * Q * (8 / 7) with hK1
  have hK10 : 0 ≤ K1 := by positivity
  have hS : ‖Obs2.nuFH R t k‖ * ‖∑ i ∈ range k, Obs2.rowS (Obs2.histCovO R t i) a‖ ≤
      K1 * (3 / 2) := by
    refine (mul_le_mul hnu (norm_sum_le _ _) (norm_nonneg _) (by positivity)).trans ?_
    rw [mul_sum]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine (sum_le_sum fun i hi => ?_).trans ((mul_sum _ _ _).symm.le.trans
      (mul_le_mul_of_nonneg_left (Obs2.geom_tail_le' hy0 hy3 k') hK10))
    have hi' := mem_range.1 hi
    have hzi := X.zpos (i + 1)
    have h3 := X.rowS_le (show i < Nh by omega) a
    have hzr := zH_ratio_up R X.hρ0 X.hρ8 t (show i + 1 ≤ k' + 1 + 1 by omega)
    have hb := mul_le_mul_of_nonneg_left h3
      (by positivity : (0 : ℝ) ≤ zp / ((L : ℝ) ^ (k' + 1)) ^ 2 * Q)
    refine hb.trans ?_
    have hr := pow_ratio_L2 hL0 (show i ≤ k' by omega)
    have e : zp / ((L : ℝ) ^ (k' + 1)) ^ 2 * Q *
        (18 * ((L : ℝ) ^ (i + 1)) ^ 2 * (R.ℓ ^ 2 / (16 * zH R t (i + 1)))) =
        (9 / 8 * R.ℓ ^ 2 * Q) * (zp / zH R t (i + 1)) *
          (((L : ℝ) ^ (i + 1)) ^ 2 / ((L : ℝ) ^ (k' + 1)) ^ 2) := by
      field_simp
      ring
    rw [e, hr]
    have hzz : zp / zH R t (i + 1) ≤ (8 / 7) * (8 / 7 : ℝ) ^ (k' - i) := by
      rw [div_le_iff₀ hzi]
      have : (8 / 7 : ℝ) ^ (k' + 1 + 1 - (i + 1)) = (8 / 7) * (8 / 7 : ℝ) ^ (k' - i) := by
        rw [← pow_succ']; congr 1; omega
      rw [this] at hzr
      linarith
    have e2 : K1 * y ^ (k' - i) = (9 / 8 * R.ℓ ^ 2 * Q) * ((8 / 7) * (8 / 7 : ℝ) ^ (k' - i)) *
        (((L : ℝ) ^ 2)⁻¹) ^ (k' - i) := by
      rw [hK1, hy, mul_pow]; ring
    rw [e2]
    have hpos : 0 ≤ 9 / 8 * R.ℓ ^ 2 * Q := by positivity
    have hq : 0 ≤ (((L : ℝ) ^ 2)⁻¹) ^ (k' - i) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzz hpos) hq
  rw [norm_mul]
  refine hS.trans ?_
  have hc1 := X.hcm
  have hc2 := X.hcz2
  have e3 : K1 * (3 / 2) = 27 / 14 * (R.ℓ ^ 2 * cmu' * g + 16 / 7 * (R.ℓ ^ 2 * cz') * g) := by
    rw [hK1, hQ]; ring
  rw [e3]
  have : R.ℓ ^ 2 * cmu' * g + 16 / 7 * (R.ℓ ^ 2 * cz') * g ≤ c * g + 16 / 7 * c * g := by
    have := mul_le_mul_of_nonneg_right hc1 hg0
    have := mul_le_mul_of_nonneg_right hc2 hg0
    nlinarith
  nlinarith

end C2Ctx

/-! ### The one-loop bubble: `Case2Bulk` (i) -/

open Step2.D2 in
/-- The third line of `Step2.D2.prop_d2_lines12` (the dressed value of `𝔩(w'_j + C'_{j+1}) - 𝔩(w'_j)`)
as a named property of the constants `(ζ̄, K, c_S)`. -/
def LcProp (L : ℕ) [NeZero L] (ζbar K cS : ℝ) : Prop :=
  ∀ (N : ℕ) (msq : ℝ) (ζ : ℕ → ℂ), 1 ≤ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    (∀ i, ‖ζ i‖ ≤ ζbar) → ∀ j, 1 ≤ j → j + 1 < N →
    ‖(lc (wp (dData L N msq ζ) j + Cp (dData L N msq ζ) (j + 1)) - lc (wp (dData L N msq ζ) j)) -
        (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
      (2 * Real.pi)⁻¹ ^ 2 * (ErrL / ((L : ℝ) ^ j) ^ 2 +
        LB * msq * (((L : ℝ) ^ j) ^ 2 + ((L : ℝ) ^ (j + 1)) ^ 2)) +
      (dData L N msq ζ).Mz (j + 1) * (4 * K + 2 * (L : ℝ) ^ 2 * K ^ 2 * (dData L N msq ζ).Mz (j + 1) +
        12 * (K + cS) * (K * (dData L N msq ζ).Mz (j + 1) + cS))

theorem lcProp_of {L : ℕ} [NeZero L] (hL : 7 ≤ L) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ K cS : ℝ, 0 ≤ K ∧ 0 ≤ cS ∧ LcProp L ζbar K cS := by
  obtain ⟨ζbar, hζ, K, cS, hK, hcS, h⟩ := Step2.D2.prop_d2_lines12 (q := 2) le_rfl hL
  exact ⟨ζbar, hζ, K, cS, hK, hcS, fun N msq ζ hN hm hm' hz j hj hjN =>
    (h (L ^ N) N msq ζ hN rfl hm hm' hz j hj hjN).2.2⟩

theorem lc_smul_tau {n : ℕ} [NeZero n] (c : ℂ) (w : DressedFRD.Sym 2 n) :
    Step2.D2.lc (c • w) = c ^ 2 * Step2.D2.lc w := by
  unfold Step2.D2.lc
  rw [Step2.D2.bl_smul_left, Step2.D2.bl_comm, Step2.D2.bl_smul_left, Step2.D2.bl_comm]; ring

theorem kmat_sum_tau {n : ℕ} [NeZero n] {ι : Type*} (s : Finset ι) (w : ι → DressedFRD.Sym 2 n) :
    DressedFRD.kmat (∑ i ∈ s, w i) = ∑ i ∈ s, DressedFRD.kmat (w i) := by
  ext x y
  simp only [DressedFRD.kmat, DressedFRD.kern_sum, Matrix.sum_apply]

theorem sum_Icc_pred {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ k : ℕ, ∑ i ∈ Icc 1 k, f (i - 1) = ∑ i ∈ range k, f i
  | 0 => by simp
  | k + 1 => by
    rw [sum_Icc_succ_top (by omega), sum_Icc_pred f k, sum_range_succ, Nat.add_sub_cancel]

theorem wp_eq_tau {n : ℕ} [NeZero n] (D : DressedFRD.Data 2 n) (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 2)
    (k : ℕ) : Step2.D2.wp D k = D.Z (k + 1) • ∑ i ∈ range k, D.Gint i := by
  unfold Step2.D2.wp Step2.D2.Cp
  rw [← sum_Icc_pred (fun i => D.Gint i) k, smul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_smul, div_mul_cancel₀ _ (DressedFRD.Data.Z_ne_zero (D := D) hζ i)]

namespace C2Ctx

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} {t : Hist.Seq (Xs R)}
  {cmu' cz' cd c : ℝ} (X : C2Ctx R Nh t cmu' cz' cd c)
include X

/-- **The bubble along the history is the dressed bubble of `DressedFRD`** (exact). -/
theorem bubble_eq (hP : R.P = Step2.D2.Pc) {k : ℕ} (hk : k < Nh) (a : Lam 2 L N) :
    Obs2.gH R t k * (Obs2.lfunC (∑ i ∈ range (k + 1), Obs2.histCovO R t i) a -
      Obs2.lfunC (∑ i ∈ range k, Obs2.histCovO R t i) a) =
    stGr R k (rawHist R k t) (t k).1 (t k).2.1 *
      (Step2.D2.lc (Step2.D2.wp (dData L N R.msq (zh R k t)) k +
          Step2.D2.Cp (dData L N R.msq (zh R k t)) (k + 1)) -
        Step2.D2.lc (Step2.D2.wp (dData L N R.msq (zh R k t)) k)) := by
  set D := dData L N R.msq (zh R k t) with hD
  have hV' : ∀ i ≤ k, ValidAt R i := fun i hi => X.hV i (by omega)
  have hZ : stZ' R (rawHist R k t) = D.Z (k + 1) := stZ'_eq_dData R hV' t
  have hC : ∀ j ≤ k + 1, ∑ i ∈ range j, Obs2.histCovO R t i =
      DressedFRD.kmat (∑ i ∈ range j, D.Gint i) := by
    intro j hj
    rw [kmat_sum_tau]
    exact sum_congr rfl fun i hi => stCov_eq_dData R hP t (by have := mem_range.1 hi; omega)
  have hζD : ∀ i, ‖D.ζ i‖ ≤ 1 / 2 := fun i =>
    ((hist_dData_hyps R hP hV' t).1 i).trans (by have := X.hρ8; linarith)
  rw [hC (k + 1) le_rfl, hC k (by omega), Obs2.lfunC_kmat, Obs2.lfunC_kmat, wp_eq_tau D hζD k]
  have hCp : Step2.D2.Cp D (k + 1) = D.Z (k + 1) • D.Gint k := by
    simp [Step2.D2.Cp]
  rw [hCp, ← smul_add, lc_smul_tau, lc_smul_tau, sum_range_succ]
  unfold Obs2.gH
  rw [hZ]
  ring

/-- The `ζ`-history after step `k` is bounded by `2c_zǧ_k` (and vanishes above `k`). -/
theorem zh_le {k : ℕ} (hk : k < Nh) (i : ℕ) : ‖zh R k t i‖ ≤ 2 * cz' * (t k).1 := by
  have hz0 : ∀ m i, m ≤ i → (rawHist R m t).ζ i = 0 := by
    intro m
    induction m with
    | zero => intro i _; rfl
    | succ m ih =>
      intro i hi
      show Function.update (rawHist R m t).ζ m (stZeta R (rawHist R m t)) i = 0
      rw [Function.update_of_ne (by omega)]
      exact ih i (by omega)
  have hb : 0 ≤ 2 * cz' * (t k).1 := by have := X.hcz; have := (X.hg k hk.le).1; positivity
  rcases Nat.lt_or_ge k i with hki | hik
  · rw [show zh R k t i = 0 from hz0 (k + 1) i hki, norm_zero]; exact hb
  · have e : zh R k t i = zetaH R i t := by
      show (rawHist R (k + 1) t).ζ i = _
      rw [rawHist_zeta_stable R t (show i < i + 1 by omega) (k + 1) (by omega)]
      show Function.update (rawHist R i t).ζ i (stZeta R (rawHist R i t)) i = _
      rw [Function.update_self]; rfl
    rw [e]
    refine (X.hζ i (by omega)).trans ?_
    have := X.hcz
    have := X.gmono hik hk.le
    gcongr

end C2Ctx

/-- `(2π)^{-2}(|A_l| + 2|B_l|)`. -/
def bubE : ℝ := (2 * Real.pi)⁻¹ ^ 2 * (|Step2.D2.ErrL| + 2 * |Step2.D2.LB|)

/-- The `M_z` part of the dressed bubble. -/
def bubF (L : ℕ) (c K cS : ℝ) : ℝ :=
  2 * c * (4 * K + 2 * (L : ℝ) ^ 2 * K ^ 2 * (2 * c) + 12 * (K + cS) * (K * (2 * c) + cS))

/-- The constant `B₁` of `Case2Bulk` (i). -/
def bubB (L : ℕ) (c K cS : ℝ) : ℝ :=
  9 / 112 * c + betaL L / 3 + bubE + 32 / 7 * c * (betaL L / 3 + 2 * bubE + bubF L c K cS) +
    bubF L c K cS

theorem bubE_nonneg : 0 ≤ bubE := by unfold bubE; positivity

theorem bubF_nonneg {L : ℕ} {c K cS : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K) (hcS : 0 ≤ cS) :
    0 ≤ bubF L c K cS := by unfold bubF; positivity

theorem betaL_div3 (L : ℕ) : betaL L / 3 = Real.log L / (2 * Real.pi) := by unfold betaL; ring

namespace C2Ctx

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} {t : Hist.Seq (Xs R)}
  {cmu' cz' cd c : ℝ} (X : C2Ctx R Nh t cmu' cz' cd c)
include X

/-- `|ǧ_k/(1+n_k) - ǧ_k| ≤ (32/7)cǧ_k²`. -/
theorem gr_sub_le {k : ℕ} (hk : k < Nh) :
    ‖stGr R k (rawHist R k t) (t k).1 (t k).2.1 - (((t k).1 : ℝ) : ℂ)‖ ≤ 32 / 7 * c * (t k).1 ^ 2 := by
  have hg0 : 0 ≤ (t k).1 := (X.hg k hk.le).1.le
  refine (norm_gr_sub_le hg0 (norm_nCor_le _ _)).trans ?_
  have hn4 := norm_nCor_hist_le R (rawHist R k t) k (t k).2.1 (X.hZw k hk)
  have hμ := X.hμ k hk.le
  have hcm := X.hcm
  have hℓ2 : 0 ≤ R.ℓ ^ 2 := sq_nonneg _
  have h1 : 4 * |(t k).2.1| * R.ℓ ^ 2 ≤ 4 * (cmu' * (t k).1) * R.ℓ ^ 2 := by gcongr
  have h2 : 4 * (cmu' * (t k).1) * R.ℓ ^ 2 ≤ 4 * c * (t k).1 := by
    have := mul_le_mul_of_nonneg_right hcm hg0
    nlinarith
  have h4 := (hn4.trans h1).trans h2
  have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 8 / 7 * (t k).1)
  nlinarith

/-- `k = 0`: `|g_0𝔩_{C_0}| ≤ (9/112)cǧ_0`. -/
theorem bubble_zero (h0 : 0 < Nh) (a : Lam 2 L N) :
    ‖Obs2.gH R t 0 * Obs2.lfunC (Obs2.histCovO R t 0) a‖ ≤ 9 / 112 * c * (t 0).1 := by
  have hl := Obs2.norm_lfunC_le (X.cov h0).1 (X.iN h0) a
  rw [show (fscale (stZ' R (rawHist R 0 t)) * R.ℓ / 4) ^ 4 =
    ((fscale (stZ' R (rawHist R 0 t)) * R.ℓ / 4) ^ 2) ^ 2 by ring, ellI_sq] at hl
  have hz1 := X.zpos 1
  have hg0 : 0 ≤ (t 0).1 := (X.hg 0 h0.le).1.le
  have hgr : ‖stGr R 0 (rawHist R 0 t) (t 0).1 (t 0).2.1‖ ≤ 8 / 7 * (t 0).1 := by
    have := norm_stGr_le R 0 (rawHist R 0 t) (t 0).1 (t 0).2.1
    rwa [abs_of_nonneg hg0] at this
  have hgH : ‖Obs2.gH R t 0‖ ≤ 8 / 7 * (t 0).1 * zH R t 1 ^ 2 := by
    unfold Obs2.gH
    rw [norm_mul, norm_pow]
    exact mul_le_mul hgr le_rfl (by positivity) (by positivity)
  rw [norm_mul]
  refine (mul_le_mul hgH hl (norm_nonneg _) (by positivity)).trans ?_
  have e : 8 / 7 * (t 0).1 * zH R t 1 ^ 2 * (18 * (R.ℓ ^ 2 / (16 * zH R t (0 + 1))) ^ 2) =
      9 / 112 * R.ℓ ^ 4 * (t 0).1 := by
    field_simp; ring
  rw [e]
  have := mul_le_mul_of_nonneg_right X.hc4 hg0
  linarith

end C2Ctx

/-- The pure assembly of `Case2Bulk` (i). -/
theorem bubble_assemble {gr Xv : ℂ} {g c₀ E F c zA : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hzA0 : 0 ≤ zA) (hzA2 : zA ≤ 2) (hE : 0 ≤ E) (hF : 0 ≤ F) (hc : 0 ≤ c) (hc₀ : 0 ≤ c₀)
    (hgr : ‖gr - (g : ℂ)‖ ≤ 32 / 7 * c * g ^ 2) (hXc : ‖Xv - (c₀ : ℂ)‖ ≤ E * zA + F * g) :
    ‖gr * Xv - (g : ℂ) * (c₀ : ℂ)‖ ≤
      (9 / 112 * c + c₀ + E + 32 / 7 * c * (c₀ + 2 * E + F) + F) * g ^ 2 +
      (9 / 112 * c + c₀ + E + 32 / 7 * c * (c₀ + 2 * E + F) + F) * g * zA := by
  have hXn : ‖Xv‖ ≤ c₀ + 2 * E + F := by
    have h1 := norm_sub_norm_le Xv (c₀ : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc₀] at h1
    have h2 : E * zA ≤ E * 2 := mul_le_mul_of_nonneg_left hzA2 hE
    have h3 : F * g ≤ F * 1 := mul_le_mul_of_nonneg_left hg1 hF
    linarith
  have e : gr * Xv - (g : ℂ) * (c₀ : ℂ) = (gr - (g : ℂ)) * Xv + (g : ℂ) * (Xv - (c₀ : ℂ)) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0]
  have t1 := mul_le_mul hgr hXn (norm_nonneg _) (by positivity)
  have t2 := mul_le_mul_of_nonneg_left hXc hg0
  obtain ⟨B, hBd⟩ : ∃ B, B = 9 / 112 * c + c₀ + E + 32 / 7 * c * (c₀ + 2 * E + F) + F := ⟨_, rfl⟩
  rw [← hBd]
  have hB1 : 32 / 7 * c * (c₀ + 2 * E + F) + F ≤ B := by
    have : 0 ≤ 9 / 112 * c := by positivity
    linarith
  have hB2 : E ≤ B := by
    have : 0 ≤ 32 / 7 * c * (c₀ + 2 * E + F) := by positivity
    have : 0 ≤ 9 / 112 * c := by positivity
    linarith
  have k1 : (32 / 7 * c * (c₀ + 2 * E + F) + F) * g ^ 2 ≤ B * g ^ 2 :=
    mul_le_mul_of_nonneg_right hB1 (sq_nonneg g)
  have k2 : E * (g * zA) ≤ B * (g * zA) := mul_le_mul_of_nonneg_right hB2 (mul_nonneg hg0 hzA0)
  have r1 : 32 / 7 * c * g ^ 2 * (c₀ + 2 * E + F) + g * (E * zA + F * g) =
      (32 / 7 * c * (c₀ + 2 * E + F) + F) * g ^ 2 + E * (g * zA) := by ring
  have r2 : B * g * zA = B * (g * zA) := by ring
  rw [r2]
  linarith

namespace C2Ctx

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ} {t : Hist.Seq (Xs R)}
  {cmu' cz' cd c : ℝ} (X : C2Ctx R Nh t cmu' cz' cd c)
include X

/-- **`Case2Bulk` (i)**: the one-loop bubble. -/
theorem bubble_le (hP : R.P = Step2.D2.Pc) {ζbar K cS : ℝ} (hLc : LcProp L ζbar K cS)
    (hK : 0 ≤ K) (hcS : 0 ≤ cS) (hmsq : 0 < R.msq)
    (hmsqN : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) {εb : ℝ}
    (hεb : ∀ j ≤ Nh, (t j).1 ≤ εb) (hζb : 2 * c * εb ≤ ζbar)
    {k : ℕ} (hk : k < Nh) (a : Lam 2 L N) :
    ‖Obs2.gH R t k * (Obs2.lfunC (∑ i ∈ range (k + 1), Obs2.histCovO R t i) a -
      Obs2.lfunC (∑ i ∈ range k, Obs2.histCovO R t i) a) -
        ((betaL L / 3 * (t k).1 : ℝ) : ℂ)‖ ≤
      bubB L c K cS * (t k).1 ^ 2 + bubB L c K cS * (t k).1 * zA L R.msq k := by
  have hL0 := X.L_pos
  have hL7 := X.L7
  have hc0 := X.c_nonneg
  have hg0 : 0 ≤ (t k).1 := (X.hg k hk.le).1.le
  have hg1 : (t k).1 ≤ 1 := (X.hg k hk.le).2
  have hc₀0 : 0 ≤ betaL L / 3 := by
    rw [betaL_div3]; have := Real.log_nonneg (show (1 : ℝ) ≤ L by linarith); positivity
  have hE := bubE_nonneg
  have hF := bubF_nonneg (L := L) hc0 hK hcS
  have hzA0 : 0 ≤ zA L R.msq k := zA_nonneg L X.hm0 k
  have hzA2 : zA L R.msq k ≤ 2 := by
    refine zA_le_two (by linarith) (le_trans ?_ X.hm)
    refine mul_le_mul_of_nonneg_left ?_ X.hm0
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega)) 2
  have ec : ((betaL L / 3 * (t k).1 : ℝ) : ℂ) = (((t k).1 : ℝ) : ℂ) * ((betaL L / 3 : ℝ) : ℂ) := by
    push_cast; ring
  rw [ec]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have e0 : Obs2.lfunC (∑ i ∈ range (0 + 1), Obs2.histCovO R t i) a -
        Obs2.lfunC (∑ i ∈ range 0, Obs2.histCovO R t i) a = Obs2.lfunC (Obs2.histCovO R t 0) a := by
      simp [Obs2.lfunC, Obs2.gpC]
    rw [e0]
    have hb := X.bubble_zero hk a
    have hcg : ‖(((t 0).1 : ℝ) : ℂ) * ((betaL L / 3 : ℝ) : ℂ)‖ = betaL L / 3 * (t 0).1 := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hg0, abs_of_nonneg hc₀0]; ring
    refine (norm_sub_le _ _).trans ?_
    rw [hcg, zA_zero, mul_one]
    have hB : 9 / 112 * c + betaL L / 3 ≤ bubB L c K cS := by
      unfold bubB
      have : 0 ≤ 32 / 7 * c * (betaL L / 3 + 2 * bubE + bubF L c K cS) := by positivity
      linarith
    have := mul_le_mul_of_nonneg_right hB hg0
    have : 0 ≤ bubB L c K cS * (t 0).1 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  rw [X.bubble_eq hP hk a]
  have hN1 : 1 ≤ N := by have := X.hN; omega
  have hkN : k + 1 < N := by have := X.hN; omega
  have hzb : ∀ i, ‖zh R k t i‖ ≤ ζbar := fun i =>
    (X.zh_le hk i).trans (by
      have := X.hcz1
      have h2 : 2 * cz' * (t k).1 ≤ 2 * c * εb := by
        have := X.hcz; have := hεb k hk.le; gcongr
      linarith)
  have hLv := hLc N R.msq (zh R k t) hN1 hmsq hmsqN hzb k hk1 hkN
  -- the `M_z` term
  have hMz : (dData L N R.msq (zh R k t)).Mz (k + 1) ≤ 2 * c * (t k).1 := by
    refine DressedFRD.Data.Mz_le (D := dData L N R.msq (zh R k t)) (by positivity) fun i hi => ?_
    refine (X.zh_le hk i).trans ?_
    have := X.hcz1; have := X.hcz
    gcongr
  have hMz0 : 0 ≤ (dData L N R.msq (zh R k t)).Mz (k + 1) :=
    DressedFRD.Data.Mz_nonneg (D := dData L N R.msq (zh R k t)) _
  generalize (dData L N R.msq (zh R k t)).Mz (k + 1) = Mz at hLv hMz hMz0
  have hMz2 : Mz ≤ 2 * c := hMz.trans (by nlinarith)
  have hT2 : Mz * (4 * K + 2 * (L : ℝ) ^ 2 * K ^ 2 * Mz + 12 * (K + cS) * (K * Mz + cS)) ≤
      bubF L c K cS * (t k).1 := by
    have hin : 4 * K + 2 * (L : ℝ) ^ 2 * K ^ 2 * Mz + 12 * (K + cS) * (K * Mz + cS) ≤
        4 * K + 2 * (L : ℝ) ^ 2 * K ^ 2 * (2 * c) + 12 * (K + cS) * (K * (2 * c) + cS) := by
      gcongr
    have := mul_le_mul hMz hin (by positivity) (by positivity)
    unfold bubF
    linarith [show 2 * c * (t k).1 * (4 * K + 2 * (L : ℝ) ^ 2 * K ^ 2 * (2 * c) +
      12 * (K + cS) * (K * (2 * c) + cS)) = 2 * c * (4 * K + 2 * (L : ℝ) ^ 2 * K ^ 2 * (2 * c) +
      12 * (K + cS) * (K * (2 * c) + cS)) * (t k).1 by ring]
  -- the `ζ = 0` term
  have hLk : (1 : ℝ) ≤ ((L : ℝ) ^ k) ^ 2 := one_le_pow₀ (one_le_pow₀ (by linarith))
  have hLkk : ((L : ℝ) ^ k) ^ 2 ≤ ((L : ℝ) ^ (k + 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by omega)) 2
  have hT1 : (2 * Real.pi)⁻¹ ^ 2 * (Step2.D2.ErrL / ((L : ℝ) ^ k) ^ 2 +
      Step2.D2.LB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2)) ≤
        bubE * zA L R.msq k := by
    rw [zA_pos L R.msq hk1, bubE]
    have a1 : Step2.D2.ErrL / ((L : ℝ) ^ k) ^ 2 ≤ |Step2.D2.ErrL| * (((L : ℝ) ^ k) ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have hm := X.hm0
    have a2 : Step2.D2.LB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2) ≤
        2 * |Step2.D2.LB| * (R.msq * ((L : ℝ) ^ (k + 1)) ^ 2) := by
      have h1 : Step2.D2.LB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2) ≤
          |Step2.D2.LB| * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2) := by
        gcongr; exact le_abs_self _
      have h2 : |Step2.D2.LB| * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2) ≤
          |Step2.D2.LB| * R.msq * (2 * ((L : ℝ) ^ (k + 1)) ^ 2) := by
        gcongr; linarith
      linarith
    have b1 : 0 ≤ 2 * |Step2.D2.LB| * (((L : ℝ) ^ k) ^ 2)⁻¹ := by positivity
    have b2 : 0 ≤ |Step2.D2.ErrL| * (R.msq * ((L : ℝ) ^ (k + 1)) ^ 2) :=
      mul_nonneg (abs_nonneg _) (mul_nonneg hm (by positivity))
    have hin : Step2.D2.ErrL / ((L : ℝ) ^ k) ^ 2 +
        Step2.D2.LB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2) ≤
        (|Step2.D2.ErrL| + 2 * |Step2.D2.LB|) *
          ((((L : ℝ) ^ k) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (k + 1)) ^ 2) := by
      have e : (|Step2.D2.ErrL| + 2 * |Step2.D2.LB|) *
          ((((L : ℝ) ^ k) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (k + 1)) ^ 2) =
          |Step2.D2.ErrL| * (((L : ℝ) ^ k) ^ 2)⁻¹ +
            2 * |Step2.D2.LB| * (R.msq * ((L : ℝ) ^ (k + 1)) ^ 2) +
          (2 * |Step2.D2.LB| * (((L : ℝ) ^ k) ^ 2)⁻¹ +
            |Step2.D2.ErrL| * (R.msq * ((L : ℝ) ^ (k + 1)) ^ 2)) := by ring
      rw [e]; linarith
    have hpi : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ ^ 2 := by positivity
    calc _ ≤ (2 * Real.pi)⁻¹ ^ 2 * ((|Step2.D2.ErrL| + 2 * |Step2.D2.LB|) *
          ((((L : ℝ) ^ k) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (k + 1)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hin hpi
      _ = _ := by ring
  have hXc := hLv.trans (add_le_add hT1 hT2)
  clear hLv hT1 hT2
  rw [← betaL_div3] at hXc
  generalize Step2.D2.lc (Step2.D2.wp (dData L N R.msq (zh R k t)) k +
      Step2.D2.Cp (dData L N R.msq (zh R k t)) (k + 1)) -
    Step2.D2.lc (Step2.D2.wp (dData L N R.msq (zh R k t)) k) = Xv at hXc ⊢
  have hgr := X.gr_sub_le hk
  generalize stGr R k (rawHist R k t) (t k).1 (t k).2.1 = gr at hgr ⊢
  exact bubble_assemble hg0 hg1 hzA0 hzA2 hE hF hc0 hc₀0 hgr hXc

end C2Ctx

end

end Spin2
