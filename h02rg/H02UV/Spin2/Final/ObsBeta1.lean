import Spin2.Final.Arboreal

set_option autoImplicit false

/-!
# The observable renormalisation condition: definitions and elementary lemmas

The renormalised inverse temperature `β_R` of `thm_arboreal_multiscale` is an internal parameter
of the renormalisation group analysis (the bracket `[bFin(1/(2β_R)), bFin(2/β_R)]`). Here it is
replaced by an observable: with the reference point `x₀ = (1/2, 0) ∈ 𝕋²` and its lattice point
`x₀,N = latPtN L N x₀`,
`obsBeta L N β = β · P_β[0 ↔ x₀,N]^{3/2}`.
On a bracket at `β_R`, the multiscale formula at `x₀,N` (scale `N − 2`) gives
`P_β[0 ↔ x₀,N] = (βt_{N−2}/β)^{2/3}(1 + O(1/βt_{N−2}))`, so `obsBeta = βt_{N−2} + O(1)`
(`ob_obsBeta_close`).

* `obsX0`, `obsX0N`, `obsBeta`, `obsF` (the normalised two-point function
  `f_N(x) = P_{β_N}[0 ↔ x_N]/P_{β_N}[0 ↔ x₀,N]`), `obsMass` (the internal mass `1/(32tL^{2N})`),
  `obsBR t i = t4^i/8` (the brackets whose union is used).
* Geometry of `x₀,N`: `obsX0N_far` (`x₀,N ≠ 0`, `|x₀,N|/L^N ≥ 1/4`), `obs_min_eq`
  (`min(j(x₀,N), N − 2) = N − 2`).
* `ob_rpow32`, `ob_obsBeta_close`, `ob_Pconn_of_obsBeta` (`obsBeta = t` gives
  `P[0 ↔ x₀,N] = (tb)^{2/3}`), `obsF_eq_clF` (`f_N = clF L t b N`), `clF_rescale`.
* `ArbScale.mono`, `ArbShort.rescale` (renormalisation `β_R → t`).
* Finite families: `ob_equiOn_of_family`, `ob_bdd_of_family`, `ob_minmax_finset`.
-/

namespace Spin2

open Step Step2 PtCorr2 Cont Loc Grassmann Step2.D2

noncomputable section

open Finset Flow2 Flow2.Hist Set Filter Topology

variable {L : ℕ} [NeZero L]

/-! ### Definitions -/

/-- The reference point `x₀ = (1/2, 0) ∈ 𝕋²`. -/
def obsX0 : UnitAddTorus (Fin 2) := torusProj ![1 / 2, 0]

variable (L) in
/-- The lattice point `x₀,N` of `x₀` in `Λ_N`. -/
def obsX0N (N : ℕ) : Lam 2 L N := latPtN L N obsX0

variable (L) in
/-- **The observable coupling** `t(β, N) = β · P_β[0 ↔ x₀,N]^{3/2}`. -/
def obsBeta (N : ℕ) (β : ℝ) : ℝ := β * Pconn L N β (obsX0N L N) ^ (3 / 2 : ℝ)

variable (L) in
/-- **The normalised two-point function** `f_N(x) = P_{β_N}[0 ↔ x_N]/P_{β_N}[0 ↔ x₀,N]` on `𝕋²`. -/
def obsF (βs : ℕ → ℝ) (N : ℕ) (x : UnitAddTorus (Fin 2)) : ℝ :=
  Pconn L N (βs N) (latPtN L N x) / Pconn L N (βs N) (obsX0N L N)

variable (L) in
/-- The internal auxiliary mass `m² = 1/(32 t L^{2N})` (`4m²L^{2N} = 1/(8t)`). -/
def obsMass (N : ℕ) (t : ℝ) : ℝ := 1 / (32 * t * (L : ℝ) ^ (2 * N))

/-- The renormalised couplings `β_R = t 4^i/8` of the brackets used (`i = 0, …, 3`). -/
def obsBR (t : ℝ) (i : ℕ) : ℝ := t * 4 ^ i / 8

theorem obsBR_zero (t : ℝ) : obsBR t 0 = t / 8 := by simp [obsBR]

theorem obsBR_three (t : ℝ) : obsBR t 3 = 8 * t := by unfold obsBR; ring

theorem obsBR_pos {t : ℝ} (ht : 0 < t) (i : ℕ) : 0 < obsBR t i := by unfold obsBR; positivity

theorem obsBR_ge {t : ℝ} (ht : 0 < t) (i : ℕ) : t / 8 ≤ obsBR t i := by
  unfold obsBR
  have : (1 : ℝ) ≤ 4 ^ i := one_le_pow₀ (by norm_num)
  rw [div_le_div_iff_of_pos_right (by norm_num)]
  nlinarith

theorem obsBR_le {t : ℝ} (ht : 0 < t) {i : ℕ} (hi : i ≤ 3) : obsBR t i ≤ 8 * t := by
  unfold obsBR
  have : (4 : ℝ) ^ i ≤ 4 ^ 3 := pow_le_pow_right₀ (by norm_num) hi
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

theorem obsBR_succ {t : ℝ} (ht : 0 < t) (i : ℕ) : 1 / (2 * obsBR t i) = 2 / obsBR t (i + 1) := by
  unfold obsBR
  rw [pow_succ]
  field_simp
  ring

theorem obsMass_spec (N : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    0 < obsMass L N t ∧ obsMass L N t * (L : ℝ) ^ (2 * N) ≤ 1 ∧
    ∀ i ≤ 3, 4 * (obsMass L N t * (L : ℝ) ^ (2 * N)) ≤ 1 / obsBR t i := by
  have ht0 : 0 < t := by linarith
  have hL : (0 : ℝ) < (L : ℝ) ^ (2 * N) :=
    pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) _
  have e : obsMass L N t * (L : ℝ) ^ (2 * N) = 1 / (32 * t) := by
    unfold obsMass; field_simp
  refine ⟨by unfold obsMass; positivity, ?_, fun i hi => ?_⟩
  · rw [e, div_le_one (by positivity)]; linarith
  · rw [e, show 4 * (1 / (32 * t)) = 1 / (8 * t) by field_simp; ring]
    exact one_div_le_one_div_of_le (obsBR_pos ht0 i) (obsBR_le ht0 hi)

/-! ### The reference point -/

theorem obsX0_norm : 1 / 2 ≤ ‖obsX0‖ := by
  have h := norm_le_pi_norm obsX0 0
  have e : ‖obsX0 0‖ = 1 / 2 := by
    show ‖((1 / 2 : ℝ) : UnitAddCircle)‖ = 1 / 2
    rw [AddCircle.norm_eq]
    simp only [inv_one, one_mul, mul_one]
    norm_num [abs_of_nonpos]
  linarith

theorem obsX0_ne_zero : obsX0 ≠ 0 := by
  intro h
  have := obsX0_norm
  rw [h, norm_zero] at this
  linarith

/-- `x₀,N ≠ 0` and `|x₀,N|/L^N ≥ 1/4` for `N ≥ 1`. -/
theorem obsX0N_far (hL : 2 ≤ L) {N : ℕ} (hN : 1 ≤ N) :
    obsX0N L N ≠ 0 ∧ 1 / 4 ≤ eucl (obsX0N L N) / (L : ℝ) ^ N := by
  have h := obsX0_norm
  have hLN : (2 : ℝ) ≤ (L : ℝ) ^ N := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
      _ ≤ (L : ℝ) ^ N := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hL) N
  have h1 : 1 / (2 * (L : ℝ) ^ N) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  obtain ⟨hne, hfar⟩ := t6_latPt_far hL N obsX0 (by linarith) (by linarith)
  exact ⟨hne, by unfold obsX0N; linarith⟩

omit [NeZero L] in
/-- `j(ℓ) ≥ N − 2` for `ℓ ≥ 1/4`. -/
theorem obs_jPhys_ge (hL : 2 ≤ L) {N : ℕ} {ℓ : ℝ} (hℓ : 1 / 4 ≤ ℓ) :
    (N : ℤ) - 2 ≤ jPhys L N ℓ := by
  unfold jPhys
  rw [Int.le_floor]
  push_cast
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have : -2 ≤ Real.logb L ℓ := by
    rw [Real.le_logb_iff_rpow_le hL1 (by linarith)]
    have e : (L : ℝ) ^ (-2 : ℝ) = 1 / (L : ℝ) ^ 2 := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
    rw [e]
    have h4 : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    exact (one_div_le_one_div_of_le (by norm_num) h4).trans hℓ
  linarith

omit [NeZero L] in
/-- `min(j_p, N − 2) = N − 2` for a scale `j_p = j(ℓ)` with `ℓ ≥ 1/4`. -/
theorem obs_min_eq (hL : 2 ≤ L) {N jp : ℕ} {ℓ : ℝ} (hℓ : 1 / 4 ≤ ℓ)
    (hj : (jp : ℤ) = jPhys L N ℓ) : min jp (N - 2) = N - 2 := by
  have := obs_jPhys_ge hL (N := N) hℓ
  rw [← hj] at this
  exact min_eq_right (by omega)

/-! ### `obsBeta` and the running coupling at scale `N − 2` -/

/-- For `|e| ≤ 1/4`: `|(1 + e)^{3/2} − 1| ≤ (9/4)|e|`. -/
theorem ob_rpow32 {e : ℝ} (he : |e| ≤ 1 / 4) :
    |(1 + e) ^ (3 / 2 : ℝ) - 1| ≤ 9 / 4 * |e| := by
  obtain ⟨h1, h2⟩ := abs_le.1 he
  rcases le_or_gt 0 e with h0 | h0
  · have hx : 1 ≤ 1 + e := by linarith
    have hu : (1 + e) ^ (3 / 2 : ℝ) ≤ (1 + e) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    rw [Real.rpow_two] at hu
    have hl : 1 ≤ (1 + e) ^ (3 / 2 : ℝ) := Real.one_le_rpow hx (by norm_num)
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    nlinarith
  · have hx : 0 < 1 + e := by linarith
    have hx1 : 1 + e ≤ 1 := by linarith
    have hu : (1 + e) ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hx.le hx1 (by norm_num)
    have hl : (1 + e) ^ (2 : ℝ) ≤ (1 + e) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num)
    rw [Real.rpow_two] at hl
    rw [abs_of_neg h0, abs_of_nonpos (by linarith)]
    nlinarith

/-- **`obsBeta ≈ βt`**: from `|P_{1/b}[0 ↔ x₀,N] − (βtb)^{2/3}| ≤ K(βtb)^{2/3}/βt` and `βt ≥ 4K`:
`|obsBeta L N (1/b) − βt| ≤ 3K`. -/
theorem ob_obsBeta_close {N : ℕ} {b βt K : ℝ} (hb : 0 < b) (hK : 0 ≤ K) (hβ : 4 * K ≤ βt)
    (hβ0 : 0 < βt)
    (hP : |Pconn L N (1 / b) (obsX0N L N) - (βt / (1 / b)) ^ (2 / 3 : ℝ)| ≤
      K * (βt / (1 / b)) ^ (2 / 3 : ℝ) / βt) :
    |obsBeta L N (1 / b) - βt| ≤ 3 * K := by
  have hθe : βt / (1 / b) = βt * b := by field_simp
  rw [hθe] at hP
  set P := Pconn L N (1 / b) (obsX0N L N) with hPd
  set θ := (βt * b) ^ (2 / 3 : ℝ) with hθd
  have hθ : 0 < θ := by positivity
  set e := (P - θ) / θ with hed
  have hPe : P = θ * (1 + e) := by rw [hed]; field_simp; ring
  have he : |e| ≤ K / βt := by
    rw [hed, abs_div, abs_of_pos hθ, div_le_iff₀ hθ]
    calc |P - θ| ≤ K * θ / βt := hP
      _ = K / βt * θ := by ring
  have hKβ : K / βt ≤ 1 / 4 := by rw [div_le_div_iff₀ hβ0 (by norm_num)]; linarith
  have he4 : |e| ≤ 1 / 4 := he.trans hKβ
  have h1e : 0 ≤ 1 + e := by linarith [(abs_le.1 he4).1]
  have hθ32 : θ ^ (3 / 2 : ℝ) = βt * b := by
    rw [hθd, ← Real.rpow_mul (by positivity)]; norm_num
  have hP32 : P ^ (3 / 2 : ℝ) = βt * b * (1 + e) ^ (3 / 2 : ℝ) := by
    rw [hPe, Real.mul_rpow hθ.le h1e, hθ32]
  have hob : obsBeta L N (1 / b) = βt * (1 + e) ^ (3 / 2 : ℝ) := by
    show 1 / b * P ^ (3 / 2 : ℝ) = βt * (1 + e) ^ (3 / 2 : ℝ)
    rw [hP32]; field_simp
  rw [hob]
  have := ob_rpow32 he4
  calc |βt * (1 + e) ^ (3 / 2 : ℝ) - βt| = βt * |(1 + e) ^ (3 / 2 : ℝ) - 1| := by
        rw [show βt * (1 + e) ^ (3 / 2 : ℝ) - βt = βt * ((1 + e) ^ (3 / 2 : ℝ) - 1) by ring,
          abs_mul, abs_of_pos hβ0]
    _ ≤ βt * (9 / 4 * |e|) := mul_le_mul_of_nonneg_left this hβ0.le
    _ ≤ βt * (9 / 4 * (K / βt)) := by gcongr
    _ = 9 / 4 * K := by field_simp
    _ ≤ 3 * K := by linarith

/-- `obsBeta L N (1/b) = t` gives `P_{1/b}[0 ↔ x₀,N] = (tb)^{2/3} = thetaEpsSq t b`. -/
theorem ob_Pconn_of_obsBeta {N : ℕ} {b t : ℝ} (hb : 0 < b)
    (h : obsBeta L N (1 / b) = t) :
    Pconn L N (1 / b) (obsX0N L N) = thetaEpsSq t b := by
  unfold obsBeta at h
  have hP0 : 0 ≤ Pconn L N (1 / b) (obsX0N L N) := (Pconn_mem (by positivity) _).1
  have h' : Pconn L N (1 / b) (obsX0N L N) ^ (3 / 2 : ℝ) = t * b := by
    calc Pconn L N (1 / b) (obsX0N L N) ^ (3 / 2 : ℝ)
        = b * (1 / b * Pconn L N (1 / b) (obsX0N L N) ^ (3 / 2 : ℝ)) := by field_simp
      _ = b * t := by rw [h]
      _ = t * b := mul_comm _ _
  unfold thetaEpsSq
  rw [← h', ← Real.rpow_mul hP0]; norm_num

/-- `P_{1/b}[0 ↔ x₀,N] > 0` when `obsBeta L N (1/b) = t > 0`. -/
theorem ob_Pconn_pos {N : ℕ} {b t : ℝ} (hb : 0 < b) (ht : 0 < t)
    (h : obsBeta L N (1 / b) = t) : 0 < Pconn L N (1 / b) (obsX0N L N) := by
  rw [ob_Pconn_of_obsBeta hb h]; unfold thetaEpsSq; positivity

/-- **`f_N = clF L t b N`** when `obsBeta L N (1/b_N) = t`. -/
theorem obsF_eq_clF {t : ℝ} {b : ℕ → ℝ} {N : ℕ} (hb : 0 < b N)
    (h : obsBeta L N (1 / b N) = t) : obsF L (fun N => 1 / b N) N = clF L t b N := by
  funext x
  unfold obsF clF
  beta_reduce
  rw [ob_Pconn_of_obsBeta hb h]

/-- `f_N(x₀) = 1`. -/
theorem obsF_obsX0 {βs : ℕ → ℝ} {N : ℕ} (h : Pconn L N (βs N) (obsX0N L N) ≠ 0) :
    obsF L βs N obsX0 = 1 := by
  unfold obsF obsX0N; exact div_self h

/-- `clF L t b N = (β_R/t)^{2/3} clF L β_R b N`. -/
theorem clF_rescale {t βR : ℝ} (ht : 0 < t) (hβR : 0 < βR) {b : ℕ → ℝ} {N : ℕ} (hb : 0 < b N)
    (x : UnitAddTorus (Fin 2)) :
    clF L t b N x = (βR / t) ^ (2 / 3 : ℝ) * clF L βR b N x := by
  unfold clF thetaEpsSq
  have e : (βR * b N) ^ (2 / 3 : ℝ) = (βR / t) ^ (2 / 3 : ℝ) * (t * b N) ^ (2 / 3 : ℝ) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; field_simp
  rw [e]
  have h1 : 0 < (βR / t) ^ (2 / 3 : ℝ) := by positivity
  have h2 : 0 < (t * b N) ^ (2 / 3 : ℝ) := by positivity
  field_simp

/-- `clF L t b N ≥ 0`. -/
theorem ob_clF_nonneg {t : ℝ} (ht : 0 < t) {b : ℕ → ℝ} {N : ℕ} (hb : 0 < b N)
    (x : UnitAddTorus (Fin 2)) : 0 ≤ clF L t b N x := t6_clF_nonneg ht hb x

/-- `csA β_R ℓ · (β_R/t)^{2/3} = csA t ℓ` for `ℓ ≤ 1`. -/
theorem ob_csA_rescale {t βR ℓ : ℝ} (ht : 0 < t) (hβR : 0 < βR) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    (βR / t) ^ (2 / 3 : ℝ) * csA βR ℓ = csA t ℓ := by
  unfold csA
  have hlam : 0 ≤ Real.log (1 / ℓ) := by
    rw [one_div, Real.log_inv]; linarith [Real.log_nonpos hℓ.le hℓ1]
  have hb1 := betaOne_pos
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  congr 1; field_simp

/-- `csA t ℓ ≥ 0` and `csRate ℓ ≥ 0` for `0 < ℓ ≤ e^{-1}`. -/
theorem ob_csA_csRate_nonneg {t ℓ : ℝ} (ht : 0 < t) (hℓ : 0 < ℓ) (hℓe : ℓ ≤ Real.exp (-1)) :
    0 ≤ csA t ℓ ∧ 0 ≤ csRate ℓ := by
  have hlam : 1 ≤ Real.log (1 / ℓ) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log hℓ hℓe
    rw [Real.log_exp] at this; linarith
  have hb1 := betaOne_pos
  constructor
  · unfold csA; exact Real.rpow_nonneg (div_nonneg (mul_nonneg hb1.le (by linarith)) ht.le) _
  · unfold csRate; exact div_nonneg (Real.log_nonneg hlam) (by linarith)

/-! ### Renormalisation `β_R → t` of the per-`N` conclusions -/

/-- `ArbScale` is monotone in `K` and `K_ε`. -/
theorem ArbScale.mono {N : ℕ} {βR K K' Kc Kε Kε' E a βε : ℝ} {β : ℕ → ℝ} (hN : 1 ≤ N)
    (hβR : 0 < βR) (hK : K ≤ K') (hKε : Kε ≤ Kε') (h : ArbScale L N βR K Kc Kε E a βε β) :
    ArbScale L N βR K' Kc Kε' E a βε β := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  refine ⟨h1, h2, h3.trans (mul_le_mul_of_nonneg_right hKε (by linarith)), h4, h5,
    fun x hx => ?_⟩
  obtain ⟨jp, hj, hbl, hP⟩ := h6 x hx
  refine ⟨jp, hj, hbl, hP.trans ?_⟩
  have hβk : 0 < β (min jp (N - 2)) := by linarith [(h4 (min jp (N - 2)) (min_le_right _ _)).1]
  have : 0 ≤ (β (min jp (N - 2)) / βε) ^ (2 / 3 : ℝ) / β (min jp (N - 2)) := by positivity
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hK this

/-- **Renormalisation of `ArbShort`**: `ArbShort` at `β_R` with `K_c` gives `ArbShort` at `t`
with `K_c'` whenever `K_c(1 + β_R + λ) ≤ K_c'(1 + t + λ)` for `λ ≥ 0`. -/
theorem ArbShort.rescale {N : ℕ} {βR t Ks Kc Kc' βε : ℝ} (hβR : 0 < βR) (ht : 0 < t)
    (hβε : 0 < βε) (hKc : 0 ≤ Kc)
    (hKc' : ∀ lam : ℝ, 0 ≤ lam → Kc * (1 + βR + lam) ≤ Kc' * (1 + t + lam))
    (h : ArbShort L N βR Ks Kc βε) : ArbShort L N t Ks Kc' βε := by
  intro x hx
  obtain ⟨hlam, hB, hC⟩ := h x hx
  set lam := Real.log (1 / (eucl x / (L : ℝ) ^ N)) with hlamd
  have hlog0 : 0 ≤ Real.log (1 + lam) := Real.log_nonneg (by linarith)
  have hδ := hKc' (Real.log (1 + lam)) hlog0
  have hb1 := betaOne_pos
  have hbl : 0 < betaOne * lam := mul_pos hb1 hlam
  have hc : 0 < (βR / t) ^ (2 / 3 : ℝ) := by positivity
  have e1 : Pconn L N βε x / (t / βε) ^ (2 / 3 : ℝ) =
      (βR / t) ^ (2 / 3 : ℝ) * (Pconn L N βε x / (βR / βε) ^ (2 / 3 : ℝ)) := by
    have : βR / βε = (βR / t) * (t / βε) := by field_simp
    rw [this, Real.mul_rpow (by positivity) (by positivity)]
    have h2 : 0 < (t / βε) ^ (2 / 3 : ℝ) := by positivity
    field_simp
  have e2 : (betaOne * lam / t) ^ (2 / 3 : ℝ) =
      (βR / t) ^ (2 / 3 : ℝ) * (betaOne * lam / βR) ^ (2 / 3 : ℝ) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; field_simp
  have hB0 : 0 ≤ (betaOne * lam / βR) ^ (2 / 3 : ℝ) := by positivity
  refine ⟨hlam, fun h2 => ?_, ?_⟩
  · have h2' : 2 * (Kc * (1 + βR + Real.log (1 + lam))) ≤ betaOne * lam := by linarith
    have hB' := hB h2'
    rw [e1, e2, ← mul_sub, abs_mul, abs_of_pos hc, mul_assoc]
    refine mul_le_mul_of_nonneg_left (hB'.trans ?_) hc.le
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hbl.le) hB0
  · rw [e1]
    calc (βR / t) ^ (2 / 3 : ℝ) * (Pconn L N βε x / (βR / βε) ^ (2 / 3 : ℝ))
        ≤ (βR / t) ^ (2 / 3 : ℝ) * ((1 + |Ks|) *
          ((betaOne * lam + Kc * (1 + βR + Real.log (1 + lam))) / βR) ^ (2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hC hc.le
      _ = (1 + |Ks|) * ((betaOne * lam + Kc * (1 + βR + Real.log (1 + lam))) / t) ^ (2 / 3 : ℝ) := by
          rw [show (betaOne * lam + Kc * (1 + βR + Real.log (1 + lam))) / t =
            (βR / t) * ((betaOne * lam + Kc * (1 + βR + Real.log (1 + lam))) / βR) by field_simp,
            Real.mul_rpow (by positivity) (by positivity)]
          ring
      _ ≤ (1 + |Ks|) * ((betaOne * lam + Kc' * (1 + t + Real.log (1 + lam))) / t) ^ (2 / 3 : ℝ) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ?_ ?_ (by norm_num)) (by positivity)
          · have : 0 ≤ Kc * (1 + βR + Real.log (1 + lam)) :=
              mul_nonneg hKc (by linarith)
            exact div_nonneg (by linarith) ht.le
          · exact div_le_div_of_nonneg_right (by linarith) ht.le

/-! ### Finite families -/

/-- A common `δ, N₀` for finitely many equicontinuous families. -/
theorem ob_equiOn_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (fs : ι → ℕ → UnitAddTorus (Fin 2) → ℝ) {r : ℝ} (hE : ∀ i ∈ s, ClEquiOn (fs i) r)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ N₀ : ℕ, ∀ i ∈ s, ∀ N ≥ N₀, ∀ x y, r ≤ dist x 0 → r ≤ dist y 0 →
      dist x y < δ → |fs i N x - fs i N y| ≤ η := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, 0, fun i hi => by simp at hi⟩
  | insert j s hj ih =>
    obtain ⟨δ₁, hδ₁, N₁, h₁⟩ := ih (fun i hi => hE i (Finset.mem_insert_of_mem hi))
    obtain ⟨δ₂, hδ₂, N₂, h₂⟩ := hE j (Finset.mem_insert_self _ _) η hη
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max N₁ N₂, fun i hi N hN x y hx hy hxy => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact h₂ N (le_trans (le_max_right _ _) hN) x y hx hy (hxy.trans_le (min_le_right _ _))
    · exact h₁ i hi N (le_trans (le_max_left _ _) hN) x y hx hy (hxy.trans_le (min_le_left _ _))

/-- **Equicontinuity of `f` from a finite family**: if for `N ≥ N₃` each `f N` is a bounded
multiple `c_i · fs_i N` of one of finitely many equicontinuous families, `f` is
equicontinuous. -/
theorem ob_equiOn_of_family {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (fs : ι → ℕ → UnitAddTorus (Fin 2) → ℝ) (c : ι → ℝ) {C r : ℝ} (hC : ∀ i ∈ s, |c i| ≤ C)
    (hE : ∀ i ∈ s, ClEquiOn (fs i) r) (f : ℕ → UnitAddTorus (Fin 2) → ℝ) (N₃ : ℕ)
    (hf : ∀ N, N₃ ≤ N → ∃ i ∈ s, ∀ x, f N x = c i * fs i N x) : ClEquiOn f r := by
  intro η hη
  obtain ⟨δ, hδ, N₀, h⟩ := ob_equiOn_finset s fs hE (show 0 < η / (|C| + 1) by positivity)
  refine ⟨δ, hδ, max N₀ N₃, fun N hN x y hx hy hxy => ?_⟩
  obtain ⟨i, hi, hfi⟩ := hf N (le_trans (le_max_right _ _) hN)
  rw [hfi x, hfi y, ← mul_sub, abs_mul]
  have h1 := h i hi N (le_trans (le_max_left _ _) hN) x y hx hy hxy
  have h2 := hC i hi
  calc |c i| * |fs i N x - fs i N y| ≤ |C| * (η / (|C| + 1)) :=
        mul_le_mul (h2.trans (le_abs_self C)) h1 (abs_nonneg _) (abs_nonneg _)
    _ ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg C]

/-- A common bound for finitely many bounded families. -/
theorem ob_bdd_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (fs : ι → ℕ → UnitAddTorus (Fin 2) → ℝ) {r : ℝ}
    (hb : ∀ i ∈ s, ∃ C, ∀ N x, r ≤ dist x 0 → |fs i N x| ≤ C) :
    ∃ C, ∀ i ∈ s, ∀ N x, r ≤ dist x 0 → |fs i N x| ≤ C := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun i hi => by simp at hi⟩
  | insert j s hj ih =>
    obtain ⟨C₁, h₁⟩ := ih (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    obtain ⟨C₂, h₂⟩ := hb j (Finset.mem_insert_self _ _)
    refine ⟨max C₁ C₂, fun i hi N x hx => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact (h₂ N x hx).trans (le_max_right _ _)
    · exact (h₁ i hi N x hx).trans (le_max_left _ _)

/-- **Boundedness of `f` from a finite family** (with a reindexing `ψ`). -/
theorem ob_bdd_of_family {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (fs : ι → ℕ → UnitAddTorus (Fin 2) → ℝ) (c : ι → ℝ) {C r : ℝ} (hC : ∀ i ∈ s, |c i| ≤ C)
    (hb : ∀ i ∈ s, ∃ C, ∀ N x, r ≤ dist x 0 → |fs i N x| ≤ C)
    (f : ℕ → UnitAddTorus (Fin 2) → ℝ) (ψ : ℕ → ℕ)
    (hf : ∀ N, ∃ i ∈ s, ∀ x, f N x = c i * fs i (ψ N) x) :
    ∃ C', ∀ N x, r ≤ dist x 0 → |f N x| ≤ C' := by
  obtain ⟨C₁, h₁⟩ := ob_bdd_finset s fs hb
  refine ⟨|C| * |C₁|, fun N x hx => ?_⟩
  obtain ⟨i, hi, hfi⟩ := hf N
  rw [hfi x, abs_mul]
  exact mul_le_mul ((hC i hi).trans (le_abs_self C)) ((h₁ i hi _ x hx).trans (le_abs_self C₁))
    (abs_nonneg _) (abs_nonneg _)

/-- A common `δ₀ ≤ δ_i`, `K' ≥ K_i` for finitely many pairs. -/
theorem ob_minmax_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) (δf Kf : ι → ℝ)
    (hδ : ∀ i ∈ s, 0 < δf i) (hK : ∀ i ∈ s, 0 ≤ Kf i) :
    ∃ δ₀ K' : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 ≤ K' ∧ ∀ i ∈ s, δ₀ ≤ δf i ∧ Kf i ≤ K' := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, 0, one_pos, le_rfl, le_rfl, fun i hi => by simp at hi⟩
  | insert j s hj ih =>
    obtain ⟨δ₁, K₁, hδ₁, hδ₁1, hK₁, h₁⟩ :=
      ih (fun i hi => hδ i (Finset.mem_insert_of_mem hi)) (fun i hi => hK i (Finset.mem_insert_of_mem hi))
    refine ⟨min δ₁ (δf j), max K₁ (Kf j), lt_min hδ₁ (hδ j (Finset.mem_insert_self _ _)),
      (min_le_left _ _).trans hδ₁1, le_trans hK₁ (le_max_left _ _), fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨min_le_right _ _, le_max_right _ _⟩
    · exact ⟨(min_le_left _ _).trans (h₁ i hi).1, (h₁ i hi).2.trans (le_max_left _ _)⟩

end

end Spin2
