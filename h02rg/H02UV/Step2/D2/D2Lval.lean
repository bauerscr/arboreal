import Step2.D2.D2Lfun

/-!
# The value of `𝔩(w_{j+1}) - 𝔩(w_j)` (`prop:d2`, second line, `ζ = 0`)

For the concrete family `Pc`, `w_j = C_{≤ j} = cov Pc m² (0, L^j/2]` (`= ∑_{k=1}^j C_k`):

* `ehat_zero`, `ehat_mem`: `ê_0 = 0`, `0 ≤ ê_T ≤ 1`;
* `ehat_vs_Ep`: `|ê_T(p) - E(2T√(λ+m²))| ≤ (C_e + C_rem/T²)(λ + m²)`;
* `lval_pointwise`: pointwise comparison of `λ(ĉ_{≤j+1}² - ĉ_{≤j}²)` with `(E_{j+1}² - E_j²)/λ`;
* `lfun_value`: `|𝔩(w_{j+1}) - 𝔩(w_j) - (1/2π) log L| ≤ A L^{-2j} + B m² (L^{2j} + L^{2(j+1)})`
  for `j ≥ 1`, `L^{j+1} + 1 < n`, `0 ≤ m² ≤ 1`, with `A, B` independent of `L, j, m, n`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

/-! ### Elementary bounds on `E` -/

/-- `K_E`, the decay constant of `E`. -/
def KE : ℝ := KH * kap ^ (3 : ℝ)

theorem KE_nonneg : 0 ≤ KE := by have := KH_nonneg; have := kap_pos; unfold KE; positivity

theorem abs_one_sub_Ep_le {y : ℝ} (hy : 0 < y) : |1 - Ep y| ≤ KE := by
  have h := Ep_decay y hy
  have h1 : (1 + y) ^ (-(3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have := KE_nonneg
  have : KH * kap ^ (3 : ℝ) * (1 + y) ^ (-(3 : ℝ)) ≤ KE := by
    rw [KE]; exact mul_le_of_le_one_right (by positivity) h1
  linarith [abs_nonneg (y * Ep' y)]

theorem abs_y_Ep'_le {y : ℝ} (hy : 0 < y) : |y * Ep' y| ≤ KE := by
  have h := Ep_decay y hy
  have h1 : (1 + y) ^ (-(3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have := KE_nonneg
  have : KH * kap ^ (3 : ℝ) * (1 + y) ^ (-(3 : ℝ)) ≤ KE := by
    rw [KE]; exact mul_le_of_le_one_right (by positivity) h1
  linarith [abs_nonneg (1 - Ep y)]

theorem abs_Ep_le_one_add {y : ℝ} (hy : 0 < y) : |Ep y| ≤ 1 + KE := by
  have := abs_one_sub_Ep_le hy
  have h := abs_sub (1 : ℝ) (1 - Ep y)
  rw [show (1 : ℝ) - (1 - Ep y) = Ep y by ring, abs_one] at h
  linarith

theorem abs_z_Hp'_le_sq {z : ℝ} (hz : 0 ≤ z) : |z * Hp' z| ≤ ψmax / c0 * z ^ 2 := by
  have hc0 := c0_pos
  rw [z_Hp']
  have h := (tsum_om_le (f := fun i => (z / 2 ^ i) ^ 2 * ψ (z / 2 ^ i) / c0)
    (A := ψmax / c0 * z ^ 2) (r := 1) zero_le_one fun i => by
      have hz' : 0 ≤ z / 2 ^ i := by positivity
      have h2 : z / 2 ^ i ≤ z := div_le_self hz (one_le_pow₀ (by norm_num))
      rw [abs_of_nonneg (by have := ψ_nonneg (z / 2 ^ i); positivity), one_pow, mul_one]
      have := ψ_le_ψmax (z / 2 ^ i)
      have := ψ_nonneg (z / 2 ^ i)
      have := ψmax_nonneg
      calc (z / 2 ^ i) ^ 2 * ψ (z / 2 ^ i) / c0 ≤ z ^ 2 * ψmax / c0 := by gcongr
        _ = ψmax / c0 * z ^ 2 := by ring).2
  rwa [Som_one, mul_one] at h

theorem abs_y_Ep'_le_sq {y : ℝ} (hy : 0 ≤ y) : |y * Ep' y| ≤ ψmax / c0 * y ^ 2 := by
  have hk := kap_pos
  have e : y * Ep' y = y / kap * Hp' (y / kap) := by rw [Ep']; ring
  rw [e]
  refine (abs_z_Hp'_le_sq (by positivity)).trans ?_
  have : (y / kap) ^ 2 ≤ y ^ 2 := by
    rw [div_pow]; exact div_le_self (sq_nonneg y) (one_le_pow₀ one_le_kap)
  have := ψmax_nonneg; have := c0_pos
  gcongr

/-- `min(a y⁴, b) ≤ 16 max(a, b) y⁴ (1+y)^{-4}`. -/
theorem min_pow_four_le {a b y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hy : 0 ≤ y) {v : ℝ}
    (h1 : v ≤ a * y ^ 4) (h2 : v ≤ b) : v ≤ 16 * (a + b) * y ^ 4 * (1 + y) ^ (-(4 : ℝ)) := by
  have hp : 0 < 1 + y := by linarith
  rw [Real.rpow_neg hp.le, show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rcases le_total y 1 with h | h
  · have : (1 + y) ^ 4 ≤ 16 := by
      calc (1 + y) ^ 4 ≤ 2 ^ 4 := by gcongr; linarith
        _ = 16 := by norm_num
    have hy4 : 0 ≤ y ^ 4 := by positivity
    calc v ≤ a * y ^ 4 := h1
      _ ≤ 16 * (a + b) * y ^ 4 * ((1 + y) ^ 4)⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg ha hy4)]
  · have : (1 + y) ^ 4 ≤ 16 * y ^ 4 := by
      calc (1 + y) ^ 4 ≤ (2 * y) ^ 4 := by gcongr; linarith
        _ = 16 * y ^ 4 := by ring
    have hy4 : 1 ≤ y ^ 4 := one_le_pow₀ h
    calc v ≤ b := h2
      _ ≤ 16 * (a + b) * y ^ 4 * ((1 + y) ^ 4)⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left this hb]

/-- `M_{Φ²}`: `|Φ_{E²}(y)| ≤ M_{Φ²} y⁴ (1+y)^{-4}`. -/
def MPhi2 : ℝ := 16 * (ψmax / (2 * c0) * (ψmax / (2 * c0) + ψmax / c0) + (1 + KE) * (1 + 2 * KE))

theorem MPhi2_nonneg : 0 ≤ MPhi2 := by
  have := ψmax_nonneg; have := c0_pos; have := KE_nonneg; unfold MPhi2; positivity

theorem Phi_Ep_sq_le {y : ℝ} (hy : 0 < y) :
    |Phi (fun y => Ep y ^ 2) (fun y => 2 * Ep y * Ep' y) y| ≤ MPhi2 * y ^ 4 * (1 + y) ^ (-(4 : ℝ)) := by
  have hA := abs_Ep_le_sq hy.le
  have hB := abs_y_Ep'_le_sq hy.le
  have hC := abs_Ep_le_one_add hy
  have hD := abs_y_Ep'_le hy
  have e : Phi (fun y => Ep y ^ 2) (fun y => 2 * Ep y * Ep' y) y = Ep y * (Ep y - y * Ep' y) := by
    simp only [Phi]; ring
  rw [e, abs_mul]
  have hA0 : 0 ≤ ψmax / (2 * c0) := by have := ψmax_nonneg; have := c0_pos; positivity
  have hB0 : 0 ≤ ψmax / c0 := by have := ψmax_nonneg; have := c0_pos; positivity
  have hs : |Ep y - y * Ep' y| ≤ |Ep y| + |y * Ep' y| := abs_sub _ _
  refine min_pow_four_le (by positivity) (by have := KE_nonneg; positivity) hy.le ?_ ?_
  · calc |Ep y| * |Ep y - y * Ep' y| ≤ (ψmax / (2 * c0) * y ^ 2) *
          (ψmax / (2 * c0) * y ^ 2 + ψmax / c0 * y ^ 2) :=
          mul_le_mul hA (hs.trans (add_le_add hA hB)) (abs_nonneg _) (by positivity)
      _ = ψmax / (2 * c0) * (ψmax / (2 * c0) + ψmax / c0) * y ^ 4 := by ring
  · have := KE_nonneg
    calc |Ep y| * |Ep y - y * Ep' y| ≤ (1 + KE) * ((1 + KE) + KE) :=
          mul_le_mul hC (hs.trans (add_le_add hC hD)) (abs_nonneg _) (by positivity)
      _ = (1 + KE) * (1 + 2 * KE) := by ring

/-- `C₄`: `E(y)² ≤ C₄ y⁴ (1+y)^{-4}`. -/
def C4 : ℝ := 16 * ((ψmax / (2 * c0)) ^ 2 + (1 + KE) ^ 2)

theorem C4_nonneg : 0 ≤ C4 := by
  have := ψmax_nonneg; have := c0_pos; have := KE_nonneg; unfold C4; positivity

theorem Ep_sq_le {y : ℝ} (hy : 0 < y) : Ep y ^ 2 ≤ C4 * y ^ 4 * (1 + y) ^ (-(4 : ℝ)) := by
  have hA := abs_Ep_le_sq hy.le
  have hC := abs_Ep_le_one_add hy
  have hA0 : 0 ≤ ψmax / (2 * c0) := by have := ψmax_nonneg; have := c0_pos; positivity
  refine min_pow_four_le (by positivity) (by have := KE_nonneg; positivity) hy.le ?_ ?_
  · calc Ep y ^ 2 = |Ep y| ^ 2 := (sq_abs _).symm
      _ ≤ (ψmax / (2 * c0) * y ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hA 2
      _ = (ψmax / (2 * c0)) ^ 2 * y ^ 4 := by ring
  · calc Ep y ^ 2 = |Ep y| ^ 2 := (sq_abs _).symm
      _ ≤ (1 + KE) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hC 2

/-! ### `ê_T` versus `E(2T√(λ+m²))` -/

theorem ehat_mem (P : PtFamily) {msq T : ℝ} (hm : 0 ≤ msq) (hT : 0 ≤ T) {p : ℂ}
    (hu : 0 < uhatC msq p) : 0 ≤ ehat P msq T p ∧ ehat P msq T p ≤ 1 := by
  have hu' : uhatC msq p ∈ Ioc (0 : ℝ) 2 := ⟨hu, (uhatC_mem hm p).2⟩
  have hu2 : uhatC msq p ∈ Icc (0 : ℝ) 2 := ⟨hu.le, hu'.2⟩
  have hint := FRD.integrableOn_Ioi P hu' (le_refl (0 : ℝ))
  have hnn : 0 ≤ ∫ t in Ioi T, t * (P.P t).eval (uhatC msq p) :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (hT.trans (le_of_lt ht)) (P.nonneg t (lt_of_le_of_lt hT ht) _ hu2)
  have hle : (∫ t in Ioi T, t * (P.P t).eval (uhatC msq p)) ≤ 1 / uhatC msq p := by
    rw [← P.integral_eq _ hu']
    refine setIntegral_mono_set hint ?_ (Eventually.of_forall (Ioi_subset_Ioi hT))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (le_of_lt ht) (P.nonneg t ht _ hu2)
  rw [ehat]
  constructor
  · have : uhatC msq p * (∫ t in Ioi T, t * (P.P t).eval (uhatC msq p)) ≤ 1 := by
      calc _ ≤ uhatC msq p * (1 / uhatC msq p) := by gcongr
        _ = 1 := by field_simp
    linarith
  · have := mul_nonneg hu.le hnn; linarith

theorem ehat_zero (P : PtFamily) {msq : ℝ} (hm : 0 ≤ msq) {p : ℂ} (hu : 0 < uhatC msq p) :
    ehat P msq 0 p = 0 := by
  rw [ehat, P.integral_eq _ ⟨hu, (uhatC_mem hm p).2⟩]
  field_simp; ring

/-- `B₁ = sup |1 - H|`. -/
def B1 : ℝ := CΨ / c0 * Som 8

theorem B1_nonneg : 0 ≤ B1 := by
  have := CΨ_nonneg; have := c0_pos; have := Som_nonneg (r := 8) (by norm_num); unfold B1; positivity

theorem abs_one_sub_Hp_le_B1 {z : ℝ} (hz : 0 ≤ z) : |1 - Hp z| ≤ B1 := by
  refine (one_sub_Hp_le hz).trans ?_
  have : ((1 + z) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  exact mul_le_of_le_one_right B1_nonneg this

/-- The constant `C_e`. -/
def Ce : ℝ := π ^ 2 * B1 / 32 + KE * (π / 2 * (π ^ 2 / 32 + 1 / 4))

theorem Ce_nonneg : 0 ≤ Ce := by
  have := B1_nonneg; have := KE_nonneg; have := pi_pos; unfold Ce; positivity

/-- Geometry of the angle variable: with `S = (4 + m²) 2 sin²(πx)`, `ρ = 2√2 π x`. -/
theorem angle_geom {x msq S : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) (hm : 0 ≤ msq)
    (hS : (4 + msq) * (2 * Real.sin (π * x) ^ 2) = S) :
    32 * x ^ 2 ≤ S ∧ 2 / π * (2 * √2 * π * x) ≤ √S ∧
      |√S - 2 * √2 * π * x| ≤ (8 * (π * x) ^ 4 + 2 * msq * (π * x) ^ 2) / (2 * √2 * π * x) ∧
      0 ≤ 1 - sinc2 x ∧ 1 - sinc2 x ≤ (π * x) ^ 2 := by
  have hpi := pi_pos
  set ρ := 2 * √2 * π * x with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ2 : ρ ^ 2 = 8 * π ^ 2 * x ^ 2 := by
    rw [hρdef]; ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring
  have hsin_lo : 2 * x ≤ Real.sin (π * x) := by
    have := Real.mul_le_sin (x := π * x) (by positivity) (by nlinarith)
    rwa [show 2 / π * (π * x) = 2 * x by field_simp] at this
  have hsin_hi : Real.sin (π * x) ≤ π * x := (Real.sin_lt (by positivity)).le
  have hsin0 : 0 < Real.sin (π * x) := by linarith
  have hd4 := sq_sub_sin_sq_le (π * x)
  have hd0 : 0 ≤ (π * x) ^ 2 - Real.sin (π * x) ^ 2 := by nlinarith
  have hS32 : 32 * x ^ 2 ≤ S := by rw [← hS]; nlinarith
  have hSpos : 0 < S := by nlinarith
  refine ⟨hS32, ?_, ?_, ?_, ?_⟩
  · rw [Real.le_sqrt (by positivity) hSpos.le, mul_pow, hρ2]
    have : (2 / π) ^ 2 * (8 * π ^ 2 * x ^ 2) = 32 * x ^ 2 := by field_simp; ring
    linarith
  · rw [le_div_iff₀ hρ0]
    have h1 : |√S - ρ| * (√S + ρ) = |S - ρ ^ 2| := by
      rw [← abs_of_pos (by positivity : 0 < √S + ρ), ← abs_mul]
      congr 1
      rw [show (√S - ρ) * (√S + ρ) = √S ^ 2 - ρ ^ 2 by ring, Real.sq_sqrt hSpos.le]
    have h2 : S - ρ ^ 2 = -(8 * ((π * x) ^ 2 - Real.sin (π * x) ^ 2)) +
        2 * msq * Real.sin (π * x) ^ 2 := by
      rw [← hS, hρ2]; ring
    have h3 : |S - ρ ^ 2| ≤ 8 * (π * x) ^ 4 + 2 * msq * (π * x) ^ 2 := by
      rw [h2]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      have : Real.sin (π * x) ^ 2 ≤ (π * x) ^ 2 := pow_le_pow_left₀ hsin0.le hsin_hi 2
      have : 2 * msq * Real.sin (π * x) ^ 2 ≤ 2 * msq * (π * x) ^ 2 := by gcongr
      linarith
    have h4 : |√S - ρ| * ρ ≤ |√S - ρ| * (√S + ρ) := by
      gcongr; linarith [Real.sqrt_nonneg S]
    linarith
  · rw [sinc2, sub_nonneg, div_le_one (by positivity)]
    exact pow_le_pow_left₀ hsin0.le hsin_hi 2
  · rw [sinc2]
    have hp : 0 < (π * x) ^ 2 := by positivity
    rw [one_sub_div hp.ne', div_le_iff₀ hp]
    nlinarith

/-- **`ê_T` versus the profile.** For `p ∈ [-π,π]² ∖ {0}`, `m² ≥ 0`, `T > 0`, with `S = λ + m²`:
`|ê_T(p) - E(2T√S)| ≤ (C_e + C_rem/T²) S`. -/
theorem ehat_vs_Ep {msq T : ℝ} (hm : 0 ≤ msq) (hT : 0 < T) {p : ℂ} (hp : p ∈ BZ) (hp0 : p ≠ 0) :
    |ehat Pc msq T p - Ep (2 * T * √(lamC p + msq))| ≤ (Ce + Crem / T ^ 2) * (lamC p + msq) := by
  have hpi := pi_pos
  have hlam : 0 < lamC p := lamC_pos hp hp0
  set S := lamC p + msq with hSdef
  have hS : 0 < S := by positivity
  set u := uhatC msq p with hudef
  have hu : u = S / (4 + msq) := uhatC_eq msq p
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu2 : u ∈ Icc (0 : ℝ) 2 := uhatC_mem hm p
  set x := xu u with hxdef
  have hx0 : 0 < x := xu_pos hu0
  have hx1 : x ≤ 1 / 2 := xu_le u
  have hsin := u_eq_two_sin_sq hu2
  rw [← hxdef] at hsin
  have hSx : (4 + msq) * (2 * Real.sin (π * x) ^ 2) = S := by
    rw [← hsin, hu]; field_simp
  obtain ⟨g1, g2, g3, g4, g5⟩ := angle_geom hx0 hx1 hm hSx
  set ρ := 2 * √2 * π * x with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ2 : ρ ^ 2 = 8 * π ^ 2 * x ^ 2 := by
    rw [hρdef]; ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring
  have r := ehat_repr hm hT hu0
  rw [← hudef, ← hxdef] at r
  have hH : Hp (T * x) = Ep (2 * T * ρ) := by
    rw [Ep, ← half_mul_eq_kap]; ring_nf
  -- the three pieces
  have e1 : |(1 - sinc2 x) * (1 - Hp (T * x))| ≤ π ^ 2 * B1 / 32 * S := by
    rw [abs_mul, abs_of_nonneg g4]
    have := abs_one_sub_Hp_le_B1 (show 0 ≤ T * x by positivity)
    have hB := B1_nonneg
    calc (1 - sinc2 x) * |1 - Hp (T * x)| ≤ (π * x) ^ 2 * B1 := mul_le_mul g5 this
          (abs_nonneg _) (by positivity)
      _ ≤ π ^ 2 * B1 / 32 * S := by
          have : (π * x) ^ 2 * B1 = π ^ 2 * B1 / 32 * (32 * x ^ 2) := by ring
          rw [this]; gcongr
  set ℓ := 2 * T * (2 / π) * ρ with hℓ
  have hℓ0 : 0 < ℓ := by positivity
  have hℓρ : ℓ ≤ 2 * T * ρ := by
    rw [hℓ, mul_assoc]
    gcongr
    calc 2 / π * ρ ≤ 1 * ρ := by gcongr; rw [div_le_one hpi]; linarith [pi_gt_three]
      _ = ρ := one_mul ρ
  have hℓS : ℓ ≤ 2 * T * √S := by rw [hℓ, mul_assoc]; gcongr
  have hmv : |Ep (2 * T * √S) - Ep (2 * T * ρ)| ≤ KE / ℓ * |2 * T * √S - 2 * T * ρ| := by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Ep) (f' := Ep')
      (s := uIcc (2 * T * ρ) (2 * T * √S)) (C := KE / ℓ)
      (fun t _ => (hasDerivAt_Ep t).hasDerivWithinAt)
      (fun t ht => by
        have hlt : ℓ ≤ t := le_trans (le_min hℓρ hℓS) ht.1
        have ht0 : 0 < t := hℓ0.trans_le hlt
        have h2 := abs_y_Ep'_le ht0
        rw [abs_mul, abs_of_pos ht0] at h2
        rw [Real.norm_eq_abs, le_div_iff₀ hℓ0]
        calc |Ep' t| * ℓ ≤ |Ep' t| * t := by gcongr
          _ = t * |Ep' t| := mul_comm _ _
          _ ≤ KE := h2)
      (convex_uIcc _ _) left_mem_uIcc right_mem_uIcc
    simpa only [Real.norm_eq_abs] using this
  have e2 : |Ep (2 * T * ρ) - Ep (2 * T * √S)| ≤ KE * (π / 2 * (π ^ 2 / 32 + 1 / 4)) * S := by
    rw [abs_sub_comm]
    have hcS : |2 * T * √S - 2 * T * ρ| = 2 * T * |√S - ρ| := by
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * T)]
    rw [hcS] at hmv
    have hK := KE_nonneg
    calc _ ≤ KE / ℓ * (2 * T * |√S - ρ|) := hmv
      _ ≤ KE / ℓ * (2 * T * ((8 * (π * x) ^ 4 + 2 * msq * (π * x) ^ 2) / ρ)) := by gcongr
      _ = KE * (π / 2 * (π ^ 2 * x ^ 2 + msq / 4)) := by
          rw [hℓ]; field_simp; rw [hρ2]; ring
      _ ≤ KE * (π / 2 * (π ^ 2 / 32 + 1 / 4)) * S := by
          rw [mul_assoc KE]
          refine mul_le_mul_of_nonneg_left ?_ hK
          have h1 : π ^ 2 * x ^ 2 ≤ π ^ 2 / 32 * S := by nlinarith
          have h2 : msq / 4 ≤ 1 / 4 * S := by linarith
          have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : (0 : ℝ) ≤ π / 2)
          nlinarith
  have huS : u ≤ S := by
    rw [hu, div_le_iff₀ (by linarith)]
    have : S * 1 ≤ S * (4 + msq) := mul_le_mul_of_nonneg_left (by linarith) hS.le
    linarith
  have e3 : Crem * u / T ^ 2 ≤ Crem / T ^ 2 * S := by
    have := Crem_nonneg
    calc Crem * u / T ^ 2 = Crem / T ^ 2 * u := by ring
      _ ≤ Crem / T ^ 2 * S := by gcongr
  have key : ehat Pc msq T p - Ep (2 * T * √S) =
      (ehat Pc msq T p - (1 - sinc2 x * (1 - Hp (T * x)))) + (1 - sinc2 x) * (1 - Hp (T * x)) +
        (Ep (2 * T * ρ) - Ep (2 * T * √S)) := by rw [hH]; ring
  rw [key]
  calc _ ≤ |ehat Pc msq T p - (1 - sinc2 x * (1 - Hp (T * x)))| +
        |(1 - sinc2 x) * (1 - Hp (T * x))| + |Ep (2 * T * ρ) - Ep (2 * T * √S)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Crem / T ^ 2 * S + π ^ 2 * B1 / 32 * S + KE * (π / 2 * (π ^ 2 / 32 + 1 / 4)) * S :=
        add_le_add (add_le_add (r.trans e3) e1) e2
    _ = (Ce + Crem / T ^ 2) * S := by rw [Ce]; ring

/-! ### The pointwise comparison for `𝔩` -/

/-- The single-scale symbol `ĉ_{≤T} = ê_T/(λ + m²)`. -/
theorem chat_zero_eq {msq T : ℝ} (hm : 0 ≤ msq) (hT : 0 ≤ T) {p : ℂ} (hS : 0 < lamC p + msq) :
    chat Pc msq (Ioc 0 T) p = ehat Pc msq T p / (lamC p + msq) := by
  have hu : 0 < uhatC msq p := by rw [uhatC_eq]; positivity
  rw [chat_eq_ehat Pc hm le_rfl hT hS, ehat_zero Pc hm hu, sub_zero]

/-- The algebraic identity behind `lval_pointwise`. -/
theorem lval_identity {A B Eb Ea Fb Fa lam msq : ℝ} (hl : 0 < lam) (hm : 0 ≤ msq) :
    lam * ((A / (lam + msq)) ^ 2 - (B / (lam + msq)) ^ 2) - lam * ((Fb / lam) ^ 2 - (Fa / lam) ^ 2) =
      lam / (lam + msq) * (((A - B) / (lam + msq) - (Eb - Ea) / (lam + msq)) * (A + B) +
        (Eb - Ea) / (lam + msq) * ((A - Eb) + (B - Ea))) +
      ((Eb ^ 2 / (lam + msq) - Fb ^ 2 / lam) - (Ea ^ 2 / (lam + msq) - Fa ^ 2 / lam)) -
      msq / (lam + msq) * ((Eb ^ 2 - Ea ^ 2) / (lam + msq)) := by
  have hS : 0 < lam + msq := by linarith
  field_simp
  ring

theorem hasDerivAt_Ep_sq (y : ℝ) : HasDerivAt (fun y => Ep y ^ 2) (2 * Ep y * Ep' y) y := by
  have := (hasDerivAt_Ep y).mul (hasDerivAt_Ep y)
  simp only [← sq] at this
  convert this using 1
  ring

/-- The pointwise bound for `𝔩`. -/
def Gl (L msq : ℝ) (j : ℕ) (p : ℂ) : ℝ :=
  2 * (K2c * Cmv * (1 + 2 * L ^ j / π ^ 2 * ‖p‖) ^ (-(3 : ℝ)) + 2 * Crem / (L ^ j) ^ 2) +
    K2c * (2 * (Ce + 4 * Crem)) * (1 + 2 * L ^ j / π * ‖p‖) ^ (-(3 : ℝ)) +
    (MPhi2 + C4) * msq * ((L ^ (j + 1)) ^ 4 * (1 + 2 * L ^ (j + 1) / π * ‖p‖) ^ (-(4 : ℝ)) +
      (L ^ j) ^ 4 * (1 + 2 * L ^ j / π * ‖p‖) ^ (-(4 : ℝ)))

theorem decay_le_of_le {α a b : ℝ} (hα : 0 ≤ α) (ha : 0 ≤ a) (hab : a ≤ b) :
    (1 + b) ^ (-α) ≤ (1 + a) ^ (-α) := decay_antitone hα ha hab

/-- **Pointwise comparison for `𝔩`.** On `[-π,π]² ∖ {0}`, `0 ≤ m² ≤ 1`, `L ≥ 1`:
`|λ(ĉ_{≤j+1}² - ĉ_{≤j}²) - λ((E_{j+1}/λ)² - (E_j/λ)²)| ≤ G_l(p)`. -/
theorem lval_pointwise {msq L : ℝ} (hm : 0 ≤ msq) (hm1 : msq ≤ 1) (hL : 1 ≤ L) (j : ℕ) {p : ℂ}
    (hp : p ∈ BZ) (hp0 : p ≠ 0) :
    |lamC p * (chat Pc msq (Ioc 0 (L ^ (j + 1) / 2)) p ^ 2 - chat Pc msq (Ioc 0 (L ^ j / 2)) p ^ 2) -
      lamC p * ((Ep (L ^ (j + 1) * √(lamC p)) / lamC p) ^ 2 - (Ep (L ^ j * √(lamC p)) / lamC p) ^ 2)| ≤
      Gl L msq j p := by
  have hpi := pi_pos
  have hL0 : 0 < L := by linarith
  set c := L ^ j with hcdef
  set c1 := L ^ (j + 1) with hc1def
  have hc : 1 ≤ c := one_le_pow₀ hL
  have hc1 : 1 ≤ c1 := one_le_pow₀ hL
  have hlam : 0 < lamC p := lamC_pos hp hp0
  set S := lamC p + msq with hSdef
  have hS : 0 < S := by positivity
  have hu : 0 < uhatC msq p := by rw [uhatC_eq]; positivity
  set s := √S with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 hS
  have hs2 : s ^ 2 = S := Real.sq_sqrt hS.le
  have hsp : 2 / π * ‖p‖ ≤ s := (sqrt_lamC_ge hp).trans (Real.sqrt_le_sqrt (by linarith))
  -- the pieces
  rw [chat_zero_eq hm (by positivity) hS, chat_zero_eq hm (by positivity) hS]
  set A := ehat Pc msq (c1 / 2) p
  set B := ehat Pc msq (c / 2) p
  set Eb := Ep (c1 * s)
  set Ea := Ep (c * s)
  rw [lval_identity (A := A) (B := B) (Eb := Eb) (Ea := Ea) hlam hm]
  have hA := ehat_mem Pc hm (T := c1 / 2) (by positivity) hu
  have hB := ehat_mem Pc hm (T := c / 2) (by positivity) hu
  have hAB : |A + B| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
  have hlS : 0 ≤ lamC p / S ∧ lamC p / S ≤ 1 := ⟨by positivity, by
    rw [div_le_one hS]; linarith⟩
  -- (1) `ĉ_{j+1}` versus `F_m`
  have h1 := chat_pointwise hm hm1 hL j hp hp0
  rw [chat_eq_ehat Pc hm (by positivity) (by rw [pow_succ]; gcongr; nlinarith) hS] at h1
  rw [← hcdef, ← hc1def, ← hSdef, ← hsdef] at h1
  -- (2) `|F_m|`
  have hD := Ep_decay.diff (by norm_num : (0 : ℝ) ≤ 3) hL (show 0 < c * s by positivity)
  rw [show L * (c * s) = c1 * s by rw [hcdef, hc1def, pow_succ]; ring] at hD
  have hFm : |(Eb - Ea) / S| ≤ K2c * (1 + 2 * c / π * ‖p‖) ^ (-(3 : ℝ)) / S := by
    rw [abs_div, abs_of_pos hS]
    gcongr
    have : |Eb - Ea| ≤ 2 * (KH * kap ^ (3 : ℝ)) * (1 + c * s) ^ (-(3 : ℝ)) := by
      have := abs_nonneg (c * s * (L * Ep' (c1 * s) - Ep' (c * s)))
      linarith
    refine this.trans (mul_le_mul_of_nonneg_left (decay_le_of_le (by norm_num) (by positivity)
      ?_) (by have := KH_nonneg; have := kap_pos; positivity))
    calc 2 * c / π * ‖p‖ = c * (2 / π * ‖p‖) := by ring
      _ ≤ c * s := by gcongr
  -- (3) `ê_T` versus `E(2T s)`
  have r1 := ehat_vs_Ep hm (T := c1 / 2) (by positivity) hp hp0
  have r2 := ehat_vs_Ep hm (T := c / 2) (by positivity) hp hp0
  rw [show 2 * (c1 / 2) = c1 by ring] at r1
  rw [show 2 * (c / 2) = c by ring] at r2
  have hCr := Crem_nonneg
  have hT1 : Crem / (c1 / 2) ^ 2 ≤ 4 * Crem := by
    have h4 : (1 : ℝ) / 4 ≤ (c1 / 2) ^ 2 := by
      have : (1 : ℝ) / 2 ≤ c1 / 2 := by linarith
      calc (1 : ℝ) / 4 = (1 / 2) ^ 2 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) this 2
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 4 * Crem)
    linarith
  have hT2 : Crem / (c / 2) ^ 2 ≤ 4 * Crem := by
    have h4 : (1 : ℝ) / 4 ≤ (c / 2) ^ 2 := by
      have : (1 : ℝ) / 2 ≤ c / 2 := by linarith
      calc (1 : ℝ) / 4 = (1 / 2) ^ 2 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) this 2
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 4 * Crem)
    linarith
  have hsum : |(A - Eb) + (B - Ea)| ≤ 2 * (Ce + 4 * Crem) * S := by
    refine (abs_add_le _ _).trans ?_
    have := Ce_nonneg
    have e1 : |A - Eb| ≤ (Ce + 4 * Crem) * S :=
      r1.trans (mul_le_mul_of_nonneg_right (by linarith) hS.le)
    have e2 : |B - Ea| ≤ (Ce + 4 * Crem) * S :=
      r2.trans (mul_le_mul_of_nonneg_right (by linarith) hS.le)
    linarith
  -- (4) the mass shift
  have m1 := mass_pointwise (h := fun y => Ep y ^ 2) (h' := fun y => 2 * Ep y * Ep' y)
    (M := MPhi2) (β := 4) (c := c1)
    (fun y _ => hasDerivAt_Ep_sq y)
    (fun y hy => Phi_Ep_sq_le hy) MPhi2_nonneg (by norm_num) (by positivity) hm hp hp0
  have m2 := mass_pointwise (h := fun y => Ep y ^ 2) (h' := fun y => 2 * Ep y * Ep' y)
    (M := MPhi2) (β := 4) (c := c)
    (fun y _ => hasDerivAt_Ep_sq y)
    (fun y hy => Phi_Ep_sq_le hy) MPhi2_nonneg (by norm_num) (by positivity) hm hp hp0
  simp only [fc] at m1 m2
  rw [← hSdef, ← hsdef] at m1 m2
  -- (5) the factor `m²/S`
  have q1 : Eb ^ 2 / S ≤ C4 * c1 ^ 4 * S * (1 + 2 * c1 / π * ‖p‖) ^ (-(4 : ℝ)) := by
    have := Ep_sq_le (show 0 < c1 * s by positivity)
    rw [div_le_iff₀ hS]
    have hdec := decay_le_of_le (α := 4) (by norm_num) (by positivity)
      (show 2 * c1 / π * ‖p‖ ≤ c1 * s by
        calc 2 * c1 / π * ‖p‖ = c1 * (2 / π * ‖p‖) := by ring
          _ ≤ c1 * s := by gcongr)
    calc Eb ^ 2 ≤ C4 * (c1 * s) ^ 4 * (1 + c1 * s) ^ (-(4 : ℝ)) := this
      _ = C4 * c1 ^ 4 * S * (1 + c1 * s) ^ (-(4 : ℝ)) * S := by
          rw [show (c1 * s) ^ 4 = c1 ^ 4 * (s ^ 2) ^ 2 by ring, hs2]; ring
      _ ≤ _ := by have := C4_nonneg; gcongr
  have q2 : Ea ^ 2 / S ≤ C4 * c ^ 4 * S * (1 + 2 * c / π * ‖p‖) ^ (-(4 : ℝ)) := by
    have := Ep_sq_le (show 0 < c * s by positivity)
    rw [div_le_iff₀ hS]
    have hdec := decay_le_of_le (α := 4) (by norm_num) (by positivity)
      (show 2 * c / π * ‖p‖ ≤ c * s by
        calc 2 * c / π * ‖p‖ = c * (2 / π * ‖p‖) := by ring
          _ ≤ c * s := by gcongr)
    calc Ea ^ 2 ≤ C4 * (c * s) ^ 4 * (1 + c * s) ^ (-(4 : ℝ)) := this
      _ = C4 * c ^ 4 * S * (1 + c * s) ^ (-(4 : ℝ)) * S := by
          rw [show (c * s) ^ 4 = c ^ 4 * (s ^ 2) ^ 2 by ring, hs2]; ring
      _ ≤ _ := by have := C4_nonneg; gcongr
  have h5 : |msq / S * ((Eb ^ 2 - Ea ^ 2) / S)| ≤
      C4 * msq * (c1 ^ 4 * (1 + 2 * c1 / π * ‖p‖) ^ (-(4 : ℝ)) +
        c ^ 4 * (1 + 2 * c / π * ‖p‖) ^ (-(4 : ℝ))) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ msq / S), sub_div]
    have hq : |Eb ^ 2 / S - Ea ^ 2 / S| ≤ Eb ^ 2 / S + Ea ^ 2 / S := by
      have := div_nonneg (sq_nonneg Eb) hS.le
      have := div_nonneg (sq_nonneg Ea) hS.le
      rw [abs_le]; constructor <;> linarith
    calc msq / S * |Eb ^ 2 / S - Ea ^ 2 / S| ≤ msq / S * (Eb ^ 2 / S + Ea ^ 2 / S) := by gcongr
      _ ≤ msq / S * (C4 * c1 ^ 4 * S * (1 + 2 * c1 / π * ‖p‖) ^ (-(4 : ℝ)) +
          C4 * c ^ 4 * S * (1 + 2 * c / π * ‖p‖) ^ (-(4 : ℝ))) := by gcongr
      _ = _ := by field_simp
  -- assemble
  have hmain : |lamC p / S * (((A - B) / S - (Eb - Ea) / S) * (A + B) +
      (Eb - Ea) / S * ((A - Eb) + (B - Ea)))| ≤
      2 * (K2c * Cmv * (1 + 2 * c / π ^ 2 * ‖p‖) ^ (-(3 : ℝ)) + 2 * Crem / c ^ 2) +
        K2c * (2 * (Ce + 4 * Crem)) * (1 + 2 * c / π * ‖p‖) ^ (-(3 : ℝ)) := by
    rw [abs_mul, abs_of_nonneg hlS.1]
    refine (mul_le_of_le_one_left (abs_nonneg _) hlS.2).trans ?_
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      have := mul_le_mul h1 hAB (abs_nonneg _) (by
        have := K2c_nonneg; have := Cmv_nonneg; positivity)
      linarith
    · rw [abs_mul]
      have hK := K2c_nonneg
      calc |(Eb - Ea) / S| * |(A - Eb) + (B - Ea)| ≤
          K2c * (1 + 2 * c / π * ‖p‖) ^ (-(3 : ℝ)) / S * (2 * (Ce + 4 * Crem) * S) :=
            mul_le_mul hFm hsum (abs_nonneg _) (by positivity)
        _ = _ := by field_simp
  have hmass : |(Eb ^ 2 / S - Ep (c1 * √(lamC p)) ^ 2 / lamC p) -
      (Ea ^ 2 / S - Ep (c * √(lamC p)) ^ 2 / lamC p)| ≤
      MPhi2 * msq * (c1 ^ 4 * (1 + 2 * c1 / π * ‖p‖) ^ (-(4 : ℝ)) +
        c ^ 4 * (1 + 2 * c / π * ‖p‖) ^ (-(4 : ℝ))) := by
    refine (abs_sub _ _).trans ?_
    have e : MPhi2 * msq * (c1 ^ 4 * (1 + 2 * c1 / π * ‖p‖) ^ (-(4 : ℝ)) +
        c ^ 4 * (1 + 2 * c / π * ‖p‖) ^ (-(4 : ℝ))) =
        MPhi2 * c1 ^ 4 * msq * (1 + 2 * c1 / π * ‖p‖) ^ (-(4 : ℝ)) +
        MPhi2 * c ^ 4 * msq * (1 + 2 * c / π * ‖p‖) ^ (-(4 : ℝ)) := by ring
    rw [e]
    exact add_le_add m1 m2
  refine (abs_sub _ _).trans ?_
  refine (add_le_add ((abs_add_le _ _).trans (add_le_add hmain hmass)) h5).trans (le_of_eq ?_)
  rw [Gl]; ring

/-! ### Integration and the value of `𝔩(w_{j+1}) - 𝔩(w_j)` -/

/-- The constant `A_l`. -/
def LA : ℝ := 2 * K2c * Cmv * Ia 3 * (π ^ 4 / 4) + 4 * Crem * (2 * π) ^ 2 +
  K2c * (2 * (Ce + 4 * Crem)) * Ia 3 * (π ^ 2 / 4)

/-- The constant `B_l`. -/
def LB : ℝ := (MPhi2 + C4) * Ia 4 * (π ^ 2 / 4)

theorem integral_Gl_le {msq L : ℝ} (hm : 0 ≤ msq) (hL : 1 ≤ L) (j : ℕ) :
    IntegrableOn (Gl L msq j) BZ ∧
      ∫ p in BZ, Gl L msq j p ≤ LA / (L ^ j) ^ 2 + LB * msq * ((L ^ j) ^ 2 + (L ^ (j + 1)) ^ 2) := by
  have hpi := pi_pos
  have hL0 : 0 < L := by linarith
  set c := L ^ j with hcdef
  set c1 := L ^ (j + 1) with hc1def
  have hc : 0 < c := by positivity
  have hc1 : 0 < c1 := by positivity
  haveI : IsFiniteMeasure (volume.restrict BZ) :=
    isFiniteMeasure_restrict.2 isCompact_BZ.measure_lt_top.ne
  have i3 : Integrable fun p : ℂ => (1 + 2 * c / π ^ 2 * ‖p‖) ^ (-(3 : ℝ)) :=
    integrable_decay_scale (by norm_num) (by positivity)
  have i3' : Integrable fun p : ℂ => (1 + 2 * c / π * ‖p‖) ^ (-(3 : ℝ)) :=
    integrable_decay_scale (by norm_num) (by positivity)
  have i41 : Integrable fun p : ℂ => (1 + 2 * c1 / π * ‖p‖) ^ (-(4 : ℝ)) :=
    integrable_decay_scale (by norm_num) (by positivity)
  have i42 : Integrable fun p : ℂ => (1 + 2 * c / π * ‖p‖) ^ (-(4 : ℝ)) :=
    integrable_decay_scale (by norm_num) (by positivity)
  have iC : IntegrableOn (fun _ : ℂ => 2 * Crem / c ^ 2) BZ :=
    integrableOn_const (isCompact_BZ.measure_lt_top.ne)
  have a1 := (i3.const_mul (K2c * Cmv)).integrableOn (s := BZ)
  have a2 := (i3'.const_mul (K2c * (2 * (Ce + 4 * Crem)))).integrableOn (s := BZ)
  have a3 := ((i41.const_mul (c1 ^ 4)).add (i42.const_mul (c ^ 4))).const_mul
    ((MPhi2 + C4) * msq) |>.integrableOn (s := BZ)
  have a0 := (a1.add iC).const_mul 2
  have hGi : IntegrableOn (Gl L msq j) BZ := by
    have := (a0.add a2).add a3
    refine IntegrableOn.congr_fun this (fun p _ => ?_) measurableSet_BZ
    simp only [Gl, Pi.add_apply, ← hcdef, ← hc1def]
  refine ⟨hGi, ?_⟩
  have b1 := integral_add (a0.add a2) a3
  have b2 := integral_add a0 a2
  have b3 := integral_add a1 iC
  have b4 := integral_add (μ := volume.restrict BZ) (i41.const_mul (c1 ^ 4)).integrableOn
    (i42.const_mul (c ^ 4)).integrableOn
  simp only [Pi.add_apply] at b1 b2 b3 b4
  have hI : ∫ p in BZ, Gl L msq j p = 2 * (K2c * Cmv * (∫ p in BZ, (1 + 2 * c / π ^ 2 * ‖p‖) ^ (-(3 : ℝ))) +
      2 * Crem / c ^ 2 * (2 * π) ^ 2) +
      K2c * (2 * (Ce + 4 * Crem)) * (∫ p in BZ, (1 + 2 * c / π * ‖p‖) ^ (-(3 : ℝ))) +
      (MPhi2 + C4) * msq * (c1 ^ 4 * (∫ p in BZ, (1 + 2 * c1 / π * ‖p‖) ^ (-(4 : ℝ))) +
        c ^ 4 * ∫ p in BZ, (1 + 2 * c / π * ‖p‖) ^ (-(4 : ℝ))) := by
    simp only [Gl, ← hcdef, ← hc1def]
    rw [b1, b2, integral_const_mul (2 : ℝ), b3, integral_const_mul, integral_const_mul,
      integral_const_mul, b4, integral_const_mul, integral_const_mul, setIntegral_const,
      volume_real_BZ, smul_eq_mul]
    ring
  rw [hI]
  have j3 := integral_BZ_decay_le (α := 3) (a := 2 * c / π ^ 2) (by norm_num) (by positivity)
  have j3' := integral_BZ_decay_le (α := 3) (a := 2 * c / π) (by norm_num) (by positivity)
  have j41 := integral_BZ_decay_le (α := 4) (a := 2 * c1 / π) (by norm_num) (by positivity)
  have j42 := integral_BZ_decay_le (α := 4) (a := 2 * c / π) (by norm_num) (by positivity)
  have hK := mul_nonneg K2c_nonneg Cmv_nonneg
  have hK2 : 0 ≤ K2c * (2 * (Ce + 4 * Crem)) := by
    have := K2c_nonneg; have := Ce_nonneg; have := Crem_nonneg; positivity
  have hM : 0 ≤ (MPhi2 + C4) * msq := by
    have := MPhi2_nonneg; have := C4_nonneg; positivity
  calc _ ≤ 2 * (K2c * Cmv * (Ia 3 / (2 * c / π ^ 2) ^ 2) + 2 * Crem / c ^ 2 * (2 * π) ^ 2) +
        K2c * (2 * (Ce + 4 * Crem)) * (Ia 3 / (2 * c / π) ^ 2) +
        (MPhi2 + C4) * msq * (c1 ^ 4 * (Ia 4 / (2 * c1 / π) ^ 2) + c ^ 4 * (Ia 4 / (2 * c / π) ^ 2)) := by
        gcongr
    _ = LA / c ^ 2 + LB * msq * (c ^ 2 + c1 ^ 2) := by
        rw [LA, LB]; field_simp; ring

theorem abs_chat_le (P : PtFamily) {msq : ℝ} (hm : 0 ≤ msq) {T : ℝ} (hT : 0 ≤ T) :
    ∃ B, ∀ p, |chat P msq (Ioc 0 T) p| ≤ B := by
  obtain ⟨K0, hK0, hK⟩ := FRD.eval_le_const P
  refine ⟨|(2 * 2 + msq)⁻¹| * (T * K0 * (T - 0)), fun p => ?_⟩
  rw [chat, abs_mul]
  gcongr
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 T)
    (f := fun t => t * (P.P t).eval (uhatC msq p)) (C := T * K0) (by simp)
    (fun t ht => by
      have he0 := P.nonneg t ht.1 _ (uhatC_mem hm p)
      have he1 := hK t ht.1 _ (uhatC_mem hm p)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht.1, abs_of_nonneg he0]
      exact mul_le_mul ht.2 he1 he0 hT)
  rw [Real.volume_real_Ioc_of_le hT, Real.norm_eq_abs] at h
  exact h

theorem integrableOn_lam_chat_sq (P : PtFamily) {msq : ℝ} (hm : 0 ≤ msq) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun p => lamC p * chat P msq (Ioc 0 T) p ^ 2) BZ := by
  obtain ⟨B, hB⟩ := abs_chat_le P hm hT
  haveI : IsFiniteMeasure (volume.restrict BZ) :=
    isFiniteMeasure_restrict.2 isCompact_BZ.measure_lt_top.ne
  refine Integrable.of_bound ((continuous_lamC.measurable.mul
    ((measurable_chat P msq _).pow_const 2)).aestronglyMeasurable) (8 * B ^ 2)
    (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (lamC_nonneg p), abs_pow]
  have := lamC_le_eight p
  have h2 : |chat P msq (Ioc 0 T) p| ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hB p) 2
  exact mul_le_mul this h2 (by positivity) (by norm_num)

/-- The `ζ = 0` constant `A` of `lfun_value`. -/
def ErrL : ℝ := (π ^ 6 / 256 + 1 / π ^ 2) * Ia 3 * (2 * (2 * (1 + KE) * KE)) + LA

/-- **`𝔩(w_{j+1}) - 𝔩(w_j)` for the concrete decomposition (`prop:d2`, second line, `ζ = 0`).**
With `w_k = C_{≤k} = cov Pc m² (0, L^k/2]` on the torus of side `n > L^{j+1} + 1`,
`0 ≤ m² ≤ 1`, `L ≥ 1`:
`|𝔩(w_{j+1}) - 𝔩(w_j) - (1/2π) log L| ≤ (2π)^{-2} (A L^{-2j} + B m² (L^{2j} + L^{2(j+1)}))`,
with `A = ErrL`, `B = LB` independent of `L, j, m, n`. -/
theorem lfun_value {n : ℕ} [NeZero n] {msq L : ℝ} (hm : 0 ≤ msq) (hm1 : msq ≤ 1) (hL : 1 ≤ L)
    (j : ℕ) (hn : L ^ (j + 1) + 1 < n) :
    |lfun (FRD.cov Pc msq (Ioc 0 (L ^ (j + 1) / 2)) :
        Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ) -
      lfun (FRD.cov Pc msq (Ioc 0 (L ^ j / 2)) :
        Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ) - Real.log L / (2 * π)| ≤
      (2 * π)⁻¹ ^ 2 * (ErrL / (L ^ j) ^ 2 + LB * msq * ((L ^ j) ^ 2 + (L ^ (j + 1)) ^ 2)) := by
  have hpi := pi_pos
  have hL0 : 0 < L := by linarith
  set c := L ^ j with hcdef
  set c1 := L ^ (j + 1) with hc1def
  have hc : 0 < c := by positivity
  have hcc1 : c ≤ c1 := by rw [hcdef, hc1def, pow_succ]; nlinarith [one_le_pow₀ (n := j) hL]
  rw [lfun_cov_eq_integral_BZ Pc hm (by positivity) (by linarith),
    lfun_cov_eq_integral_BZ Pc hm (by positivity) (by linarith)]
  set Ib := fun p => lamC p * chat Pc msq (Ioc 0 (c1 / 2)) p ^ 2
  set Ia' := fun p => lamC p * chat Pc msq (Ioc 0 (c / 2)) p ^ 2
  set F0 := fun z : ℂ => lamC z * ((Ep (c1 * √(lamC z)) / lamC z) ^ 2 -
    (Ep (c * √(lamC z)) / lamC z) ^ 2)
  have iB : IntegrableOn Ib BZ := integrableOn_lam_chat_sq Pc hm (by positivity)
  have iA : IntegrableOn Ia' BZ := integrableOn_lam_chat_sq Pc hm (by positivity)
  -- integrability of `F₀`
  have hE2 : Profile (fun y => Ep y * Ep y) 0 1 := by
    have := Ep_profile.mul Ep_profile; norm_num at this; exact this
  have hd2 : ∀ y, 0 < y → HasDerivAt (fun y => Ep y * Ep y) (2 * Ep y * Ep' y) y := fun y _ => by
    convert (hasDerivAt_Ep y).mul (hasDerivAt_Ep y) using 1; ring
  have hi : IntegrableOn (fun y => (Ep (L * y) * Ep (L * y) - Ep y * Ep y) / y) (Ioi 0) := by
    have := hE2.integrableOn one_pos hL
    simpa using this
  have iF : IntegrableOn F0 BZ := by
    have := lattice_integrableOn (h := fun y => Ep (L * y) * Ep (L * y) - Ep y * Ep y)
      (h' := fun y => L * (2 * Ep (L * y) * Ep' (L * y)) - 2 * Ep y * Ep' y)
      (fun y hy => hasDerivAt_scale_diff hd2 hL0 hy)
      (fun y hy => (Ep_decay.sq (by norm_num)).diff (by norm_num) hL hy) hi
      (by norm_num : (2 : ℝ) < 3) hc
    simp only [show ∀ x, L * (c * x) = c1 * x from fun x => by rw [hcdef, hc1def, pow_succ]; ring]
      at this
    refine this.congr_fun (fun z _ => ?_) measurableSet_BZ
    simp only [F0]
    rcases eq_or_ne (lamC z) 0 with h0 | h0
    · simp [h0]
    · field_simp
  have h1 := lattice_l Ep_profile (fun y _ => hasDerivAt_Ep y) Ep_decay (by norm_num) hL j
  rw [← hcdef, ← hc1def] at h1
  obtain ⟨-, hG⟩ := integral_Gl_le hm hL j
  obtain ⟨hGi, -⟩ := integral_Gl_le hm hL j
  rw [← hcdef, ← hc1def] at hG
  have h2 : |∫ p in BZ, ((Ib p - Ia' p) - F0 p)| ≤ ∫ p in BZ, Gl L msq j p := by
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => abs_nonneg _) hGi ?_)
    have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := ae_iff.2 (by simp)
    filter_upwards [ae_restrict_mem measurableSet_BZ, ae_restrict_of_ae hne] with p hp hp0
    have := lval_pointwise hm hm1 hL j hp hp0
    simp only [Ib, Ia', F0, ← hcdef, ← hc1def, mul_sub] at this ⊢
    convert this using 2
  have hsplit : ((2 * π) ^ 2)⁻¹ * (∫ p in BZ, Ib p) - ((2 * π) ^ 2)⁻¹ * ∫ p in BZ, Ia' p =
      (2 * π)⁻¹ ^ 2 * (∫ p in BZ, F0 p) + (2 * π)⁻¹ ^ 2 * ∫ p in BZ, ((Ib p - Ia' p) - F0 p) := by
    have s1 := integral_sub (iB.sub iA) iF
    have s2 := integral_sub iB iA
    simp only [Pi.sub_apply] at s1 s2
    rw [s1, s2, inv_pow]; ring
  have hp2 : (0 : ℝ) < (2 * π)⁻¹ ^ 2 := by positivity
  rw [hsplit]
  calc _ = |((2 * π)⁻¹ ^ 2 * (∫ p in BZ, F0 p) - Real.log L / (2 * π)) +
        (2 * π)⁻¹ ^ 2 * ∫ p in BZ, ((Ib p - Ia' p) - F0 p)| := by congr 1; ring
    _ ≤ (2 * π)⁻¹ ^ 2 * ((π ^ 6 / 256 + 1 / π ^ 2) * Ia 3 * (2 * (2 * (1 + KH * kap ^ (3 : ℝ)) *
          (KH * kap ^ (3 : ℝ)))) / c ^ 2) +
        (2 * π)⁻¹ ^ 2 * (LA / c ^ 2 + LB * msq * (c ^ 2 + c1 ^ 2)) := by
        refine (abs_add_le _ _).trans (add_le_add h1 ?_)
        rw [abs_mul, abs_of_pos hp2]
        exact mul_le_mul_of_nonneg_left (h2.trans hG) hp2.le
    _ = _ := by rw [ErrL, KE]; ring

/-! ### `w_j = ∑_{k ≤ j} C_k` -/

section Sum

variable {n : ℕ} [NeZero n]

theorem cov_Ioc_add (P : PtFamily) {msq : ℝ} (hm : 0 ≤ msq) {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) :
    (FRD.cov P msq (Ioc a b) : Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ) +
      FRD.cov P msq (Ioc b c) = FRD.cov P msq (Ioc a c) := by
  simp only [FRD.cov]
  rw [fmat_add]
  congr 1; funext m
  simp only [wt]
  rw [← mul_add, ← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (FRD.integrableOn_Ioc P (uhat_mem hm m) b ha)
    (FRD.integrableOn_Ioc P (uhat_mem hm m) c (ha.trans hab)), Ioc_union_Ioc_eq_Ioc hab hbc]

/-- `w_j = ∑_{k=1}^j C_k = cov (0, L^j/2]` for `j ≥ 1`. -/
theorem sum_Cj_eq_cov (P : PtFamily) {msq L : ℝ} (hm : 0 ≤ msq) (hL : 1 ≤ L) :
    ∀ j : ℕ, 1 ≤ j → ∑ k ∈ Finset.Icc 1 j,
      (FRD.Cj P msq L k : Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ) =
        FRD.cov P msq (Ioc 0 (L ^ j / 2))
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp [FRD.Cj, FRD.lowEnd]
  | j + 2, _ => by
    rw [Finset.sum_Icc_succ_top (by omega), sum_Cj_eq_cov P hm hL (j + 1) (by omega), FRD.Cj,
      FRD.lowEnd_succ L (by omega)]
    exact cov_Ioc_add P hm (by positivity) (by positivity)
      (by have h := pow_le_pow_right₀ hL (show j + 1 ≤ j + 2 by omega); linarith)

/-- **`prop:d2`, second line, `ζ = 0`**, with `w_j = ∑_{k=1}^j C_k`. -/
theorem lfun_value_sum {msq L : ℝ} (hm : 0 ≤ msq) (hm1 : msq ≤ 1) (hL : 1 ≤ L)
    {j : ℕ} (hj : 1 ≤ j) (hn : L ^ (j + 1) + 1 < n) :
    |lfun (∑ k ∈ Finset.Icc 1 (j + 1),
        (FRD.Cj Pc msq L k : Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ)) -
      lfun (∑ k ∈ Finset.Icc 1 j,
        (FRD.Cj Pc msq L k : Matrix (Grassmann.Torus 2 n) (Grassmann.Torus 2 n) ℝ)) -
      Real.log L / (2 * π)| ≤
      (2 * π)⁻¹ ^ 2 * (ErrL / (L ^ j) ^ 2 + LB * msq * ((L ^ j) ^ 2 + (L ^ (j + 1)) ^ 2)) := by
  rw [sum_Cj_eq_cov Pc hm hL (j + 1) (by omega), sum_Cj_eq_cov Pc hm hL j hj]
  exact lfun_value hm hm1 hL j hn

end Sum

end

end Step2.D2
