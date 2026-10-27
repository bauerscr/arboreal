import DressedFRD.LatticeMoment
import FRD.Bounds

/-!
# The decomposition of `FRD` is a standard decomposition (`def:std`), in every `d ≥ 2`

For a family `P : PtFamily` the pieces of `FRD.Decomp` have symbols
* `Ĉ_k = wt P m² (L^{k-1}/2, L^k/2]` for `1 ≤ k < N` (`(0, L/2]` for `k = 1`),
* `Ĉ_N = wt P m² (L^{N-1}/2, ∞)` (this is `C_{N,N}`, including the zero mode).

`frd_stdFull` proves (S1)–(S5) for these, uniformly in `N`, `m² > 0` and `n = L^N`, in every
dimension `d ≥ 2`. The bounds are proved in Fourier space from `PtFamily.bound` alone:
* `wt_Ioc_le`: `Ĉ_k(p) ≤ B L^{2k}` and `Ĉ_k(p) (L^{k-1}|p|_σ)^{2r} ≤ B (16d)^r L^{2k}`;
* (S4) then follows from the lattice sum `avg_pnorm_pow_le`, since
  `|∇^β C_k(0,x)| ≤ ⨍ |σ_β| Ĉ_k` and `|σ_β| ≤ |p|_σ^{|β|}`;
* (S5) follows from `∫_T^∞ t (1 + c t²)^{-(r+1)} dt = (1 + cT²)^{-r}/(2cr)` and
  `|p|_σ ≥ 4/n` for `p ≠ 0`.
The position-space bounds `FRD.Cj_bound` (which assume `d ≥ 3`) are not used.
-/

namespace DressedFRD

noncomputable section

open Finset MeasureTheory Set FRD Grassmann Filter Topology

variable (P : PtFamily)

variable {d n : ℕ} [NeZero n]

/-- The symbols `Ĉ_k` of the decomposition of `FRD`. -/
def frdC (msq : ℝ) (L N : ℕ) (k : ℕ) : Torus d n → ℝ :=
  if k < N then wt P msq (Ioc (lowEnd L k) ((L : ℝ) ^ k / 2)) else wt P msq (Ioi (lowEnd L N))

/-! ### Elementary facts -/

theorem pnorm_sq_le_lam (hd : 1 ≤ d) (m : Torus d n) : pnorm m ^ 2 ≤ lam m := by
  obtain ⟨i, hi⟩ := exists_pnorm_eq hd m
  rw [hi, char_unitT, norm_stdAddChar_sub_one_sq]
  exact cosk_term_le m i

theorem pnorm_le_two (hd : 1 ≤ d) (m : Torus d n) : pnorm m ≤ 2 := by
  obtain ⟨i, hi⟩ := exists_pnorm_eq hd m
  rw [hi]
  calc ‖char m (unitT i) - 1‖ ≤ ‖char m (unitT i)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [FRD.norm_char, norm_one]; norm_num

theorem pnorm_ge_of_ne (hd : 1 ≤ d) {m : Torus d n} (hm : m ≠ 0) : 4 / (n : ℝ) ≤ pnorm m := by
  have h1 := pnorm_ge hd m
  have h2 : 1 ≤ supNorm m := Nat.one_le_iff_ne_zero.2 fun h => hm ((supNorm_eq_zero_iff m).1 h)
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  calc 4 / (n : ℝ) ≤ 4 * (supNorm m : ℝ) / n := by
        gcongr; have : (1 : ℝ) ≤ supNorm m := by exact_mod_cast h2
        linarith
    _ ≤ _ := h1

/-- `P_t(û) ≤ K (1 + t² λ/(4d))^{-r}`, uniformly in `n` and `m² ≥ 0`. -/
theorem eval_uhat_le' (hd : 1 ≤ d) (r : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) [NeZero n] (msq : ℝ), 0 ≤ msq → ∀ t : ℝ, 0 < t →
      ∀ m : Torus d n, (P.P t).eval (uhat msq m) ≤ K * ((1 + t ^ 2 * lam m / (4 * d)) ^ r)⁻¹ := by
  obtain ⟨K, hK0, hK⟩ := eval_uhat_le P (d := d) hd (s := 0) le_rfl r
  refine ⟨K, hK0, fun n _ msq hmsq t ht m => ?_⟩
  have := hK n msq hmsq t ht m
  simpa using this


/-! ### The integrals in `t` -/

theorem hasDerivAt_aux {c : ℝ} (hc : 0 < c) {r : ℕ} (hr : 1 ≤ r) (t : ℝ) :
    HasDerivAt (fun t : ℝ => -((1 + c * t ^ 2) ^ r)⁻¹ / (2 * c * r))
      (t * ((1 + c * t ^ 2) ^ (r + 1))⁻¹) t := by
  have hg : HasDerivAt (fun t : ℝ => 1 + c * t ^ 2) (c * (2 * t)) t := by
    have := ((hasDerivAt_pow 2 t).const_mul c).const_add 1
    simpa using this
  have hpos : 0 < 1 + c * t ^ 2 := by positivity
  have h1 := (hg.pow r).inv (pow_ne_zero r hpos.ne')
  have h2 := h1.neg.div_const (2 * c * r)
  simp only [Pi.pow_apply, Pi.inv_apply] at h2
  convert h2 using 1
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem tendsto_aux {c : ℝ} (hc : 0 < c) {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (fun t : ℝ => -((1 + c * t ^ 2) ^ r)⁻¹ / (2 * c * r)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => 1 + c * t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 ((tendsto_pow_atTop (by norm_num)).const_mul_atTop hc)
  have h2 : Tendsto (fun t : ℝ => (1 + c * t ^ 2) ^ r) atTop atTop :=
    (tendsto_pow_atTop (by omega)).comp h1
  have h3 := (h2.inv_tendsto_atTop.neg).div_const (2 * c * r)
  simpa using h3

theorem integrableOn_aux {c : ℝ} (hc : 0 < c) {r : ℕ} (hr : 1 ≤ r) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun t : ℝ => t * ((1 + c * t ^ 2) ^ (r + 1))⁻¹) (Ioi T) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hasDerivAt_aux hc hr t)
    (fun t ht => by have : 0 ≤ t := hT.trans ht.le; positivity) (tendsto_aux hc hr)

theorem integral_aux {c : ℝ} (hc : 0 < c) {r : ℕ} (hr : 1 ≤ r) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in Ioi T, t * ((1 + c * t ^ 2) ^ (r + 1))⁻¹ = ((1 + c * T ^ 2) ^ r)⁻¹ / (2 * c * r) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun t _ => hasDerivAt_aux hc hr t)
    (fun t ht => by have : 0 ≤ t := hT.trans ht.le; positivity) (tendsto_aux hc hr)]
  ring

/-- `Ĉ` on `(a, b]`: `wt ≤ B b² (1 + a² λ/(4d))^{-r}`. -/
theorem wt_Ioc_le (hd : 1 ≤ d) (r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) [NeZero n] (msq : ℝ), 0 ≤ msq → ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ∀ m : Torus d n, wt P msq (Ioc a b) m ≤ B * b ^ 2 * ((1 + a ^ 2 * lam m / (4 * d)) ^ r)⁻¹ := by
  obtain ⟨K, hK0, hK⟩ := eval_uhat_le' P (d := d) hd r
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨(2 * (d : ℝ))⁻¹ * K, by positivity, fun n _ msq hmsq a b ha hab m => ?_⟩
  have hl := lam_nonneg m
  set X := ((1 + a ^ 2 * lam m / (4 * d)) ^ r)⁻¹
  have hX0 : 0 ≤ X := by positivity
  have hpt : ∀ t ∈ Ioc a b, t * (P.P t).eval (uhat msq m) ≤ b * (K * X) := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
    have h1 := hK n msq hmsq t ht0 m
    have h2 : ((1 + t ^ 2 * lam m / (4 * d)) ^ r)⁻¹ ≤ X := by
      refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ r)
      have : a ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ha ht.1.le 2
      have : a ^ 2 * lam m ≤ t ^ 2 * lam m := mul_le_mul_of_nonneg_right this hl
      have : a ^ 2 * lam m / (4 * d) ≤ t ^ 2 * lam m / (4 * d) := by gcongr
      linarith
    have hP0 := P.nonneg t ht0 _ (uhat_mem hmsq m)
    exact mul_le_mul ht.2 (h1.trans (mul_le_mul_of_nonneg_left h2 hK0)) hP0 (by linarith)
  have hint : (∫ t in Ioc a b, t * (P.P t).eval (uhat msq m)) ≤ (b - a) * (b * (K * X)) := by
    have := setIntegral_mono_on (integrableOn_Ioc P (uhat_mem hmsq m) b ha)
      (integrableOn_const (C := b * (K * X)) (by simp)) measurableSet_Ioc hpt
    refine this.trans (le_of_eq ?_)
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  have hI0 : 0 ≤ ∫ t in Ioc a b, t * (P.P t).eval (uhat msq m) :=
    setIntegral_nonneg measurableSet_Ioc (fun t ht => mul_nonneg (ha.trans ht.1.le)
      (P.nonneg t (lt_of_le_of_lt ha ht.1) _ (uhat_mem hmsq m)))
  have hinv : (2 * d + msq)⁻¹ ≤ (2 * (d : ℝ))⁻¹ := inv_anti₀ (by positivity) (by linarith)
  unfold wt
  calc (2 * d + msq)⁻¹ * (∫ t in Ioc a b, t * (P.P t).eval (uhat msq m))
      ≤ (2 * (d : ℝ))⁻¹ * ((b - a) * (b * (K * X))) :=
        mul_le_mul hinv hint hI0 (by positivity)
    _ ≤ (2 * (d : ℝ))⁻¹ * (b * (b * (K * X))) := by
        gcongr
        · have : 0 ≤ b := ha.trans hab
          positivity
        · linarith
    _ = _ := by ring


/-- `Ĉ` on `(T, ∞)`: `wt ≤ B (1 + cT²)^{-r} / (2cr)` with `c = λ/(4d)`. -/
theorem wt_Ioi_le (hd : 1 ≤ d) {r : ℕ} (hr : 1 ≤ r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) [NeZero n] (msq : ℝ), 0 < msq → ∀ T : ℝ, 0 ≤ T →
      ∀ m : Torus d n, 0 < lam m →
        wt P msq (Ioi T) m ≤
          B * (((1 + lam m / (4 * d) * T ^ 2) ^ r)⁻¹ / (2 * (lam m / (4 * d)) * r)) := by
  obtain ⟨K, hK0, hK⟩ := eval_uhat_le' P (d := d) hd (r + 1)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨(2 * (d : ℝ))⁻¹ * K, by positivity, fun n _ msq hmsq T hT m hl => ?_⟩
  set c := lam m / (4 * d)
  have hc : 0 < c := by positivity
  have hpt : ∀ t ∈ Ioi T, t * (P.P t).eval (uhat msq m) ≤
      K * (t * ((1 + c * t ^ 2) ^ (r + 1))⁻¹) := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt hT ht
    have h1 := hK n msq hmsq.le t ht0 m
    have e : t ^ 2 * lam m / (4 * d) = c * t ^ 2 := by simp only [c]; ring
    rw [e] at h1
    calc t * (P.P t).eval (uhat msq m) ≤ t * (K * ((1 + c * t ^ 2) ^ (r + 1))⁻¹) :=
          mul_le_mul_of_nonneg_left h1 ht0.le
      _ = _ := by ring
  have hint : (∫ t in Ioi T, t * (P.P t).eval (uhat msq m)) ≤
      K * (((1 + c * T ^ 2) ^ r)⁻¹ / (2 * c * r)) := by
    have := setIntegral_mono_on (integrableOn_Ioi P (uhat_mem_Ioc hmsq m) hT)
      ((integrableOn_aux hc hr hT).const_mul K) measurableSet_Ioi hpt
    refine this.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_aux hc hr hT]
  have hI0 : 0 ≤ ∫ t in Ioi T, t * (P.P t).eval (uhat msq m) :=
    setIntegral_nonneg measurableSet_Ioi (fun t ht => mul_nonneg (hT.trans (le_of_lt ht))
      (P.nonneg t (lt_of_le_of_lt hT ht) _ (uhat_mem hmsq.le m)))
  have hinv : (2 * d + msq)⁻¹ ≤ (2 * (d : ℝ))⁻¹ := inv_anti₀ (by positivity) (by linarith)
  unfold wt
  calc (2 * d + msq)⁻¹ * (∫ t in Ioi T, t * (P.P t).eval (uhat msq m))
      ≤ (2 * (d : ℝ))⁻¹ * (K * (((1 + c * T ^ 2) ^ r)⁻¹ / (2 * c * r))) :=
        mul_le_mul hinv hint hI0 (by positivity)
    _ = _ := by ring


/-! ### (S1)–(S3) -/

variable {msq : ℝ} {L N : ℕ}

theorem frdC_of_lt {k : ℕ} (hk : k < N) :
    frdC P (d := d) (n := n) msq L N k = wt P msq (Ioc (lowEnd L k) ((L : ℝ) ^ k / 2)) := by
  simp [frdC, hk]

theorem frdC_N : frdC P (d := d) (n := n) msq L N N = wt P msq (Ioi (lowEnd L N)) := by
  simp [frdC]

theorem frdC_nonneg (hmsq : 0 ≤ msq) (k : ℕ) (m : Torus d n) : 0 ≤ frdC P msq L N k m := by
  unfold frdC
  split_ifs
  · exact wt_nonneg P hmsq measurableSet_Ioc
      (fun t ht => lt_of_le_of_lt (lowEnd_nonneg (by positivity) k) ht.1) m
  · exact wt_nonneg P hmsq measurableSet_Ioi
      (fun t ht => lt_of_le_of_lt (lowEnd_nonneg (by positivity) N) ht) m

theorem frdC_even (k : ℕ) (m : Torus d n) : frdC P msq L N k (-m) = frdC P msq L N k m := by
  unfold frdC; split_ifs <;> exact wt_even P _ _ m

theorem frdC_sum (hmsq : 0 < msq) (hL : 1 ≤ L) (hN : 1 ≤ N) (m : Torus d n) :
    ∑ k ∈ Finset.Icc 1 N, frdC P msq L N k m = (lam m + msq)⁻¹ := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hI : Finset.Icc 1 N = insert N (Finset.Ico 1 N) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [hI, sum_insert (by simp), frdC_N,
    sum_congr rfl fun k hk => congrFun (frdC_of_lt P (Finset.mem_Ico.1 hk).2) m]
  simp only [wt, ← Finset.mul_sum, ← mul_add]
  have hs := integral_split P (uhat_mem_Ioc hmsq m) hL' hN
  rw [add_comm] at hs
  rw [hs, P.integral_eq _ (uhat_mem_Ioc hmsq m), uhat]
  have h1 : 0 < lam m + msq := by linarith [lam_nonneg m]
  have h2 : (0 : ℝ) < 2 * d + msq := by positivity
  field_simp

theorem kern_ofR_eq_fmat {w : Torus d n → ℝ} (hw : Even' w) (x : Torus d n) :
    kern (ofR w) x = ((fmat w x 0 : ℝ) : ℂ) := by
  unfold kern ofR fmat
  rw [sub_zero, Complex.ofReal_mul, sum_char_real hw x]; push_cast; rfl

theorem frdC_range (hmsq : 0 < msq) (hL : 1 ≤ L) {k : ℕ} (hk : k < N) :
    2 * rng (ofR (frdC P (d := d) (n := n) msq L N k)) < L ^ k := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hpos : 1 ≤ L ^ k := Nat.one_le_pow _ _ (by omega)
  have h : rng (ofR (frdC P (d := d) (n := n) msq L N k)) ≤ (L ^ k - 1) / 2 := by
    refine rng_le_iff.2 fun x hx => ?_
    rw [kern_ofR_eq_fmat (fun m => frdC_even P k m), frdC_of_lt P hk]
    have hx' : (L : ℝ) ^ k / 2 ≤ supNorm (x - 0) := by
      rw [sub_zero]
      have : L ^ k ≤ 2 * supNorm x := by omega
      have : ((L ^ k : ℕ) : ℝ) ≤ 2 * (supNorm x : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have := Cj_finiteRange P hmsq.le hL' k hx'
    simp only [Cj, cov] at this
    rw [this]; simp
  omega

theorem frd_stdHyp (hmsq : 0 < msq) (hL : 1 ≤ L) (hN : 1 ≤ N) :
    StdHyp L N msq (frdC P (d := d) (n := n) msq L N) :=
  ⟨hmsq, frdC_nonneg P hmsq.le, frdC_sum P hmsq hL hN, fun _ _ hk => frdC_range P hmsq hL hk⟩


/-! ### (S4): Fourier moments -/

/-- `X (R |p|_σ)^{2r} ≤ (16d)^r` for `X = (1 + a² λ/(4d))^{-r}`, `R = L^{k-1}`, `a = lowEnd L k`. -/
theorem decay_factor (hd : 1 ≤ d) (hL : 1 ≤ L) (r : ℕ) {k : ℕ} (hk : 1 ≤ k) (m : Torus d n) :
    ((1 + lowEnd L k ^ 2 * lam m / (4 * d)) ^ r)⁻¹ * ((L : ℝ) ^ (k - 1) * pnorm m) ^ (2 * r) ≤
      (16 * d) ^ r := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hl := lam_nonneg m
  have hp := pnorm_nonneg m
  have hp2 := pnorm_sq_le_lam hd m
  have hX : 0 < (1 + lowEnd L k ^ 2 * lam m / (4 * d)) ^ r := by positivity
  rw [inv_mul_le_iff₀ hX, pow_mul, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ r
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1 : k = 1 := by omega
    subst hk1
    simp only [lowEnd, le_refl, if_true, Nat.sub_self, pow_zero, one_mul]
    have := pnorm_le_two hd m
    have : pnorm m ^ 2 ≤ 4 := by nlinarith
    have e : (1 + (0 : ℝ) ^ 2 * lam m / (4 * d)) * (16 * d) = 16 * d := by ring
    rw [e]; linarith
  · have hlow : lowEnd L k = (L : ℝ) ^ (k - 1) / 2 := by
      simp only [lowEnd, show ¬ k ≤ 1 by omega, if_false]
    rw [hlow]
    have hR : 0 ≤ ((L : ℝ) ^ (k - 1)) ^ 2 := by positivity
    have h1 : ((L : ℝ) ^ (k - 1) * pnorm m) ^ 2 ≤ ((L : ℝ) ^ (k - 1)) ^ 2 * lam m := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hp2 hR
    have h2 : (1 + ((L : ℝ) ^ (k - 1) / 2) ^ 2 * lam m / (4 * d)) * (16 * (d : ℝ)) =
        16 * d + ((L : ℝ) ^ (k - 1)) ^ 2 * lam m := by
      field_simp; ring
    rw [h2]
    nlinarith

/-- The Fourier moments of `Ĉ_k`, `1 ≤ k < N`:
`⨍ |p|_σ^a Ĉ_k ≤ c L^{-(k-1)(d-2+a)}` for `a ≤ 2M`. -/
theorem frd_moment (hd : 1 ≤ d) {L : ℕ} (hL : 7 ≤ L) (M : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : ℕ) [NeZero n] (N : ℕ) (msq : ℝ), n = L ^ N → 0 < msq →
      ∀ k, 1 ≤ k → k < N → ∀ a ≤ 2 * M,
        avg (fun m : Torus d n => pnorm m ^ a * frdC P msq L N k m) ≤
          c * (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2 + a))) := by
  set r := M + d + 1
  obtain ⟨B, hB0, hB⟩ := wt_Ioc_le P (d := d) hd r
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : 1 ≤ L := by omega
  set E := 1 + (16 * (d : ℝ)) ^ r * (2 * 5 ^ d * (Real.pi / 2) ^ (2 * r : ℝ))
  have hE : 0 ≤ E := by positivity
  refine ⟨B / 4 * (L : ℝ) ^ 2 * E, by positivity, fun n _ N msq hn hmsq k hk1 hkN a ha => ?_⟩
  set R : ℝ := (L : ℝ) ^ (k - 1)
  have hR : 0 < R := by positivity
  set Bk := B * ((L : ℝ) ^ k / 2) ^ 2
  have hBk : 0 ≤ Bk := by positivity
  have hw := frdC_of_lt P (d := d) (n := n) (msq := msq) (L := L) hkN
  have hlow0 := lowEnd_nonneg (show (0 : ℝ) ≤ L by positivity) k
  have hlowb : lowEnd L k ≤ (L : ℝ) ^ k / 2 := by
    have := lowEnd_le (show (1 : ℝ) ≤ L by exact_mod_cast hL1) k; linarith [this]
  have hpt : ∀ m : Torus d n, frdC P msq L N k m ≤
      Bk * ((1 + lowEnd L k ^ 2 * lam m / (4 * d)) ^ r)⁻¹ := fun m => by
    rw [hw]; exact hB n msq hmsq.le _ _ hlow0 hlowb m
  have hX1 : ∀ m : Torus d n, ((1 + lowEnd L k ^ 2 * lam m / (4 * d)) ^ r)⁻¹ ≤ 1 := fun m => by
    have := lam_nonneg m
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by
      have : 0 ≤ lowEnd L k ^ 2 * lam m / (4 * d) := by positivity
      linarith))
  have hnR : 7 * R ≤ n := by
    rw [hn]; push_cast
    have : (L : ℝ) ^ N = (L : ℝ) ^ 2 * R * (L : ℝ) ^ (N - k - 1) := by
      simp only [R]; rw [← pow_add, ← pow_add]; congr 1; omega
    rw [this]
    have h1 : (1 : ℝ) ≤ (L : ℝ) ^ (N - k - 1) := one_le_pow₀ (by exact_mod_cast hL1)
    have h7 : (7 : ℝ) ≤ L := by exact_mod_cast hL
    have : (7 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    have : 7 * R ≤ (L : ℝ) ^ 2 * R := by nlinarith
    nlinarith
  have hab : (d : ℝ) + a < 2 * r := by
    have : (a : ℝ) ≤ 2 * M := by exact_mod_cast ha
    simp only [r]; push_cast; linarith
  have hmain := avg_pnorm_pow_le (d := d) (n := n) hd (w := frdC P msq L N k) (B := Bk)
    (B' := Bk * (16 * d) ^ r) (R := R) a r hR hnR hab (frdC_nonneg P hmsq.le k)
    (fun m => (hpt m).trans (mul_le_of_le_one_right hBk (hX1 m))) (by positivity)
    (fun m _ => by
      calc frdC P msq L N k m * (R * pnorm m) ^ (2 * r)
          ≤ Bk * ((1 + lowEnd L k ^ 2 * lam m / (4 * d)) ^ r)⁻¹ * (R * pnorm m) ^ (2 * r) :=
            mul_le_mul_of_nonneg_right (hpt m) (pow_nonneg (mul_nonneg hR.le (pnorm_nonneg m)) _)
        _ = Bk * (((1 + lowEnd L k ^ 2 * lam m / (4 * d)) ^ r)⁻¹ * (R * pnorm m) ^ (2 * r)) := by
            ring
        _ ≤ Bk * (16 * d) ^ r :=
            mul_le_mul_of_nonneg_left (decay_factor hd hL1 r hk1 m) hBk)
  -- the constant
  have htail : tailC d (2 * r - a) ≤ 2 * 5 ^ d * (Real.pi / 2) ^ (2 * r : ℝ) := by
    have hda : (d : ℝ) + 1 ≤ 2 * r - a := by
      have : (a : ℝ) ≤ 2 * M := by exact_mod_cast ha
      simp only [r]; push_cast; linarith
    refine (tailC_le hda).trans ?_
    have : (Real.pi / 2) ^ ((2 * r : ℝ) - a) ≤ (Real.pi / 2) ^ (2 * r : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
        (by have := Nat.cast_nonneg (α := ℝ) a; linarith)
    have h5 : (0 : ℝ) ≤ 2 * 5 ^ d := by positivity
    simpa using mul_le_mul_of_nonneg_left this h5
  have hRpow : Bk * R ^ (-((a : ℝ) + d)) =
      B / 4 * (L : ℝ) ^ 2 * (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2 + a))) := by
    simp only [Bk, R]
    rw [← Real.rpow_natCast (L : ℝ) (k - 1), ← Real.rpow_mul hL0.le, div_pow, ← pow_mul,
      ← Real.rpow_natCast (L : ℝ) (k * 2), ← Real.rpow_natCast (L : ℝ) 2]
    have : (L : ℝ) ^ ((k * 2 : ℕ) : ℝ) * (L : ℝ) ^ (((k - 1 : ℕ) : ℝ) * -((a : ℝ) + d)) =
        (L : ℝ) ^ ((2 : ℕ) : ℝ) * (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2 + a))) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
      congr 1; push_cast [Nat.cast_sub hk1]; ring
    calc B * ((L : ℝ) ^ ((k * 2 : ℕ) : ℝ) / 2 ^ 2) * (L : ℝ) ^ (((k - 1 : ℕ) : ℝ) * -((a : ℝ) + d))
        = B / 4 * ((L : ℝ) ^ ((k * 2 : ℕ) : ℝ) *
            (L : ℝ) ^ (((k - 1 : ℕ) : ℝ) * -((a : ℝ) + d))) := by ring
      _ = _ := by rw [this]; ring
  have hRp : 0 ≤ R ^ (-((a : ℝ) + d)) := Real.rpow_nonneg hR.le _
  calc avg (fun m : Torus d n => pnorm m ^ a * frdC P msq L N k m)
      ≤ (Bk + Bk * (16 * d) ^ r * tailC d (2 * r - a)) * R ^ (-((a : ℝ) + d)) := hmain
    _ ≤ (Bk * E) * R ^ (-((a : ℝ) + d)) := by
        refine mul_le_mul_of_nonneg_right ?_ hRp
        simp only [E]
        have : Bk * (16 * d) ^ r * tailC d (2 * r - a) ≤
            Bk * (16 * d) ^ r * (2 * 5 ^ d * (Real.pi / 2) ^ (2 * r : ℝ)) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
        nlinarith
    _ = E * (Bk * R ^ (-((a : ℝ) + d))) := by ring
    _ = _ := by rw [hRpow]; ring


/-! ### (S5) -/

/-- `Ĉ_N(p) (1 + L^{N-1}|p|_σ)^M ≤ c L^d L^{2(N-1)}` for `p ≠ 0`. -/
theorem frd_S5 (hd : 2 ≤ d) {L : ℕ} (hL : 7 ≤ L) {M : ℕ} (hM : 1 ≤ M) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : ℕ) [NeZero n] (N : ℕ) (msq : ℝ), n = L ^ N → 1 ≤ N → 0 < msq →
      ∀ m : Torus d n, m ≠ 0 →
        frdC P msq L N N m * (1 + (L : ℝ) ^ (N - 1) * pnorm m) ^ M ≤
          c * (L : ℝ) ^ d * (L : ℝ) ^ (2 * (N - 1)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, hB0, hB⟩ := wt_Ioi_le P (d := d) hd1 hM
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  refine ⟨B * (32 * d) ^ M * (2 * d) / (16 * M), by positivity,
    fun n _ N msq hn hN hmsq m hm => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  set p := pnorm m
  have hp4 : 4 / (n : ℝ) ≤ p := pnorm_ge_of_ne hd1 hm
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp4
  have hlam : p ^ 2 ≤ lam m := pnorm_sq_le_lam hd1 m
  have hl0 : 0 < lam m := lt_of_lt_of_le (by positivity) hlam
  set c := lam m / (4 * d)
  have hc : 0 < c := by positivity
  set T := lowEnd L N
  have hT : 0 ≤ T := lowEnd_nonneg (by positivity) N
  set y := (L : ℝ) ^ (N - 1) * p
  have hy0 : 0 ≤ y := by positivity
  have h1 : frdC P msq L N N m ≤ B * (((1 + c * T ^ 2) ^ M)⁻¹ / (2 * c * M)) := by
    rw [frdC_N]; exact hB n msq hmsq T hT m hl0
  have hX : 0 < 1 + c * T ^ 2 := by positivity
  -- `1 + y ≤ 32 d (1 + c T²)`
  have h2 : 1 + y ≤ 32 * d * (1 + c * T ^ 2) := by
    rcases Nat.lt_or_ge N 2 with hN2 | hN2
    · have : N = 1 := by omega
      subst this
      have hy : y = p := by simp [y]
      have := pnorm_le_two hd1 m
      have : 0 ≤ c * T ^ 2 := by positivity
      nlinarith
    · have hT' : T = (L : ℝ) ^ (N - 1) / 2 := by
        simp only [T, lowEnd, show ¬ N ≤ 1 by omega, if_false]
      have hcT : y ^ 2 / (16 * d) ≤ c * T ^ 2 := by
        rw [hT']
        simp only [y, c]
        rw [div_le_iff₀ (by positivity)]
        have : ((L : ℝ) ^ (N - 1) * p) ^ 2 ≤ ((L : ℝ) ^ (N - 1)) ^ 2 * lam m := by
          rw [mul_pow]; exact mul_le_mul_of_nonneg_left hlam (by positivity)
        have e : lam m / (4 * d) * ((L : ℝ) ^ (N - 1) / 2) ^ 2 * (16 * d) =
            ((L : ℝ) ^ (N - 1)) ^ 2 * lam m := by field_simp; ring
        linarith
      have e2 : 32 * (d : ℝ) * (1 + y ^ 2 / (16 * d)) = 32 * d + 2 * y ^ 2 := by
        field_simp; ring
      have : 1 + y ≤ 32 * (d : ℝ) * (1 + y ^ 2 / (16 * d)) := by
        rw [e2]; nlinarith [sq_nonneg (y - 1)]
      nlinarith
  have h2M : (1 + y) ^ M ≤ (32 * d) ^ M * (1 + c * T ^ 2) ^ M := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h2 M
  -- `(2cM)^{-1} ≤ 2d n²/(16M)`
  have h3 : (2 * c * M)⁻¹ ≤ 2 * d * (n : ℝ) ^ 2 / (16 * M) := by
    have hp2 : 16 / (n : ℝ) ^ 2 ≤ lam m := by
      have : (4 / (n : ℝ)) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (by positivity) hp4 2
      have e : (4 / (n : ℝ)) ^ 2 = 16 / (n : ℝ) ^ 2 := by ring
      linarith
    simp only [c]
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hp2
    field_simp
    nlinarith
  have hn2 : (n : ℝ) ^ 2 ≤ (L : ℝ) ^ d * (L : ℝ) ^ (2 * (N - 1)) := by
    rw [hn]; push_cast
    rw [← pow_mul, show N * 2 = 2 + 2 * (N - 1) by omega, pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL1 hd) (by positivity)
  have hC0 := frdC_nonneg P (L := L) (N := N) hmsq.le N m
  calc frdC P msq L N N m * (1 + y) ^ M
      ≤ B * (((1 + c * T ^ 2) ^ M)⁻¹ / (2 * c * M)) * ((32 * d) ^ M * (1 + c * T ^ 2) ^ M) :=
        mul_le_mul h1 h2M (by positivity) (by positivity)
    _ = B * (32 * d) ^ M * (2 * c * M)⁻¹ := by
        field_simp
    _ ≤ B * (32 * d) ^ M * (2 * d * (n : ℝ) ^ 2 / (16 * M)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = B * (32 * d) ^ M * (2 * d) / (16 * M) * (n : ℝ) ^ 2 := by ring
    _ ≤ B * (32 * d) ^ M * (2 * d) / (16 * M) * ((L : ℝ) ^ d * (L : ℝ) ^ (2 * (N - 1))) :=
        mul_le_mul_of_nonneg_left hn2 (by positivity)
    _ = _ := by ring

/-! ### The instance -/

/-- **The decomposition of `FRD` is a standard decomposition** (`def:std`), in every `d ≥ 2`,
uniformly in `N ≥ 1`, `m² > 0` and `n = L^N`. -/
theorem frd_stdFull (hd : 2 ≤ d) {L : ℕ} (hL : 7 ≤ L) {q M : ℕ} (hM : q + d + 1 ≤ M) :
    ∃ cS : ℝ, 0 ≤ cS ∧ ∀ (n : ℕ) [NeZero n] (N : ℕ) (msq : ℝ), 1 ≤ N → n = L ^ N → 0 < msq →
      StdFull L N q M msq cS (frdC P (d := d) (n := n) msq L N) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c₄, hc₄, h₄⟩ := frd_moment P hd1 hL M
  obtain ⟨c₅, hc₅, h₅⟩ := frd_S5 P (d := d) hd hL (M := M) (by omega)
  refine ⟨max c₄ c₅, le_max_of_le_left hc₄, fun n _ N msq hN hn hmsq => ?_⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  refine ⟨frd_stdHyp P hmsq (by omega) hN, hM, le_max_of_le_left hc₄, ?_, ?_, ?_⟩
  · -- (S4a)
    intro k hk1 hkN β hβ x
    rw [dop_kern]
    refine (norm_kern_le_avg _ x).trans ?_
    have hmono : (avg fun m : Torus d n => ‖sigma β m * ofR (frdC P msq L N k) m‖) ≤
        avg (fun m : Torus d n => pnorm m ^ Grassmann.mabs β * frdC P msq L N k m) := by
      refine avg_mono fun m => ?_
      rw [norm_mul, ofR, Complex.norm_real, Real.norm_of_nonneg (frdC_nonneg P hmsq.le k m)]
      exact mul_le_mul_of_nonneg_right (norm_sigma_le_pnorm β m) (frdC_nonneg P hmsq.le k m)
    refine hmono.trans ((h₄ n N msq hn hmsq k hk1 hkN _ (by omega)).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hL0.le _)
  · -- (S4b)
    intro k hk1 hkN α hα
    have hmono : (avg fun m : Torus d n => ‖sigma α m‖ ^ 2 * frdC P msq L N k m) ≤
        avg (fun m : Torus d n => pnorm m ^ (2 * Grassmann.mabs α) * frdC P msq L N k m) := by
      refine avg_mono fun m => mul_le_mul_of_nonneg_right ?_ (frdC_nonneg P hmsq.le k m)
      rw [pow_mul', ]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sigma_le_pnorm α m) 2
    have hb := h₄ n N msq hn hmsq k hk1 hkN (2 * Grassmann.mabs α) (by omega)
    rw [show ((2 * Grassmann.mabs α : ℕ) : ℝ) = 2 * (Grassmann.mabs α : ℝ) by push_cast; ring] at hb
    exact hmono.trans (hb.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hL0.le _)))
  · -- (S5)
    intro m hm
    refine (h₅ n N msq hn hN hmsq m hm).trans ?_
    have : 0 ≤ (L : ℝ) ^ d * (L : ℝ) ^ (2 * (N - 1)) := by positivity
    calc c₅ * (L : ℝ) ^ d * (L : ℝ) ^ (2 * (N - 1)) = c₅ * ((L : ℝ) ^ d * (L : ℝ) ^ (2 * (N - 1))) := by ring
      _ ≤ max c₄ c₅ * ((L : ℝ) ^ d * (L : ℝ) ^ (2 * (N - 1))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) this
      _ = _ := by ring

end

end DressedFRD
