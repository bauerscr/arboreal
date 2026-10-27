import FRD.BoundsFourier
import FRD.BoundsLattice

/-!
# The scaling estimates `e:C-bd`

With `ϑ_j(m²) = (2d+m²)^{-1} (1 + m² L^{2j}/(2d+m²))^{-s}`:

* `Cj_bound`: `|∇^{α_1}_x ∇^{α_2}_y C_{j+1}(x,y)| ≤ K ϑ_j L^{-(d-2+|α_1|+|α_2|) j}` for
  `L^{j+1} ≤ n` (uniformly in the torus);
* `CN_bound`: the same for `C_N` (with `j + 1 = N`) on `Λ_N = (ℤ/L^Nℤ)^d`.

The proof is by Fourier analysis: `abs_nabC_fmat_le` bounds the derivatives by
`|Λ|^{-1} ∑_k |w(k)| λ(k)^{A/2}`, `A = |α_1| + |α_2|`; the symbol `w` is an integral over the
scales `t` of `t P_t(û(k))`, and for each `t` the lattice sum is `O((1 + t)^{-(d+A)})` times
`(1 + t^2 m²/(2d+m²))^{-s}` (`psi_bound`, from `latt_small`, `latt_large`); integrating over
`t > lowEnd` gives the claim.
-/

namespace FRD

noncomputable section

open Finset MeasureTheory Set Grassmann Filter Topology

variable (P : PtFamily)

/-! ### An elementary integral -/

theorem hasDerivAt_inv_pow {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t : ℝ => -((1 + t) ^ ((-(r : ℤ)))) / r) (((1 + t) ^ (r + 1))⁻¹) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := (hasDerivAt_id t).const_add 1
  have h2 := (hasDerivAt_zpow (-(r : ℤ)) (1 + t) (Or.inl (by positivity))).comp t h1
  have h3 := (h2.neg).div_const (r : ℝ)
  convert h3 using 1
  · have hr' : (r : ℝ) ≠ 0 := by positivity
    have hpos : (1 + t) ≠ 0 := by positivity
    rw [show -(r : ℤ) - 1 = -((r + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    push_cast
    field_simp

theorem tendsto_inv_pow {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (fun t : ℝ => -((1 + t) ^ ((-(r : ℤ)))) / r) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => (1 + t) ^ ((-(r : ℤ)))) atTop (𝓝 0) :=
    (tendsto_zpow_atTop_zero (by omega)).comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
  simpa using (h1.neg).div_const (r : ℝ)

theorem integrableOn_inv_pow {r : ℕ} (hr : 1 ≤ r) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => ((1 + t) ^ (r + 1))⁻¹) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun t ht => hasDerivAt_inv_pow hr (ha.trans ht))
    (fun t ht => by have : 0 ≤ t := ha.trans ht.le; positivity) (tendsto_inv_pow hr)

/-- `∫_a^∞ (1 + t)^{-(r+1)} dt = (1 + a)^{-r} / r`. -/
theorem integral_inv_pow {r : ℕ} (hr : 1 ≤ r) {a : ℝ} (ha : 0 ≤ a) :
    ∫ t in Ioi a, ((1 + t) ^ (r + 1))⁻¹ = ((1 + a) ^ r)⁻¹ / r := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun t ht => hasDerivAt_inv_pow hr (ha.trans ht))
    (fun t ht => by have : 0 ≤ t := ha.trans ht.le; positivity) (tendsto_inv_pow hr)]
  rw [zpow_neg, zpow_natCast]; ring

/-! ### The bound on `P_t(û(k))` -/

variable {d n : ℕ} [NeZero n]

theorem uhat_ge_rho {msq : ℝ} (hmsq : 0 ≤ msq) (m : Torus d n) :
    msq / (2 * d + msq) ≤ uhat msq m := by
  unfold uhat
  exact div_le_div_of_nonneg_right (by linarith [lam_nonneg m]) (by positivity)

theorem uhat_ge_lam (hd : 1 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) (m : Torus d n) :
    lam m / (4 * d) ≤ uhat msq m := by
  unfold uhat
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [lam_nonneg m, lam_le m]

/-- `P_t(û) ≤ K (1 + t^2 m²/(2d+m²))^{-s} (1 + t^2 λ/(4d))^{-(A+d)}`. -/
theorem eval_uhat_le (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) [NeZero n] (msq : ℝ), 0 ≤ msq → ∀ t : ℝ, 0 < t →
      ∀ m : Torus d n, (P.P t).eval (uhat msq m) ≤
        K * (1 + t ^ 2 * (msq / (2 * d + msq))) ^ (-s) * ((1 + t ^ 2 * lam m / (4 * d)) ^ N)⁻¹ := by
  obtain ⟨K, hK⟩ := P.bound (s + N) (by positivity)
  refine ⟨max K 0, le_max_right _ _, fun n _ msq hmsq t ht m => ?_⟩
  have hu := uhat_mem hmsq m
  have h1 := hK t ht _ hu
  set u := uhat msq m
  have hpos : 0 < 1 + t ^ 2 * u := by have := hu.1; positivity
  have e : (1 + t ^ 2 * u) ^ (-(s + N)) = (1 + t ^ 2 * u) ^ (-s) * ((1 + t ^ 2 * u) ^ N)⁻¹ := by
    rw [neg_add, Real.rpow_add hpos, Real.rpow_neg hpos.le (N : ℝ), Real.rpow_natCast]
  have h2 : (1 + t ^ 2 * u) ^ (-s) ≤ (1 + t ^ 2 * (msq / (2 * d + msq))) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (by gcongr; exact uhat_ge_rho hmsq m) (by linarith)
  have h3 : ((1 + t ^ 2 * u) ^ N)⁻¹ ≤ ((1 + t ^ 2 * lam m / (4 * d)) ^ N)⁻¹ := by
    have := lam_nonneg m
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ N)
    rw [mul_div_assoc]
    gcongr
    exact uhat_ge_lam hd hmsq m
  calc (P.P t).eval u ≤ K * (1 + t ^ 2 * u) ^ (-(s + N)) := h1
    _ ≤ max K 0 * ((1 + t ^ 2 * u) ^ (-s) * ((1 + t ^ 2 * u) ^ N)⁻¹) := by
        rw [e]; gcongr; exact le_max_left _ _
    _ ≤ max K 0 * ((1 + t ^ 2 * (msq / (2 * d + msq))) ^ (-s) *
          ((1 + t ^ 2 * lam m / (4 * d)) ^ N)⁻¹) := by
        gcongr
    _ = _ := by ring

/-- `λ^{A/2} (1 + t^2 λ/(4d))^{-(A+d)} ≤ (√(4d)/t)^A (1 + t^2 λ/(4d))^{-d}`. -/
theorem sqrt_pow_mul_le (hd : 1 ≤ d) (A : ℕ) {t : ℝ} (ht : 0 < t) {l : ℝ} (hl : 0 ≤ l) :
    Real.sqrt l ^ A * ((1 + t ^ 2 * l / (4 * d)) ^ (A + d))⁻¹ ≤
      (Real.sqrt (4 * d) / t) ^ A * ((1 + t ^ 2 * l / (4 * d)) ^ d)⁻¹ := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set X := t ^ 2 * l / (4 * d) with hX
  have hX0 : 0 ≤ X := by positivity
  have h1 : Real.sqrt l ≤ Real.sqrt (4 * d) / t * (1 + X) := by
    have h2 : Real.sqrt l ≤ Real.sqrt (4 * d) / t * Real.sqrt (1 + X) := by
      rw [div_mul_eq_mul_div, ← Real.sqrt_mul (by positivity), le_div_iff₀ ht]
      rw [show t = Real.sqrt (t ^ 2) by rw [Real.sqrt_sq ht.le], ← Real.sqrt_mul hl]
      refine Real.sqrt_le_sqrt ?_
      have : 4 * (d : ℝ) * (1 + X) = 4 * d + t ^ 2 * l := by rw [hX]; field_simp
      rw [this]; nlinarith [sq_nonneg t]
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  calc Real.sqrt l ^ A * ((1 + X) ^ (A + d))⁻¹
      ≤ (Real.sqrt (4 * d) / t * (1 + X)) ^ A * ((1 + X) ^ (A + d))⁻¹ := by
        gcongr
    _ = (Real.sqrt (4 * d) / t) ^ A * ((1 + X) ^ d)⁻¹ := by
        rw [mul_pow, pow_add]; field_simp

theorem sqrt_pow_mul_le' (A N : ℕ) (m : Torus d n) {t : ℝ} :
    Real.sqrt (lam m) ^ A * ((1 + t ^ 2 * lam m / (4 * d)) ^ N)⁻¹ ≤ Real.sqrt (4 * d) ^ A := by
  have hl := lam_nonneg m
  have h1 : Real.sqrt (lam m) ^ A ≤ Real.sqrt (4 * d) ^ A :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (lam_le m)) A
  have h2 : ((1 + t ^ 2 * lam m / (4 * d)) ^ N)⁻¹ ≤ 1 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp
    · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by
        have : 0 ≤ t ^ 2 * lam m / (4 * d) := by positivity
        linarith))
  calc _ ≤ Real.sqrt (4 * d) ^ A * 1 := by
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := mul_one _

/-- The lattice sum for fixed `t`:
`|Λ|^{-1} ∑_{k ∈ T} P_t(û(k)) λ(k)^{A/2} ≤ C (1 + t^2 m²/(2d+m²))^{-s} (1 + t)^{-(d+A)}`, if
`t ≤ n` or the zero mode is not in `T`. -/
theorem psi_bound (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) [NeZero n] (msq : ℝ), 0 ≤ msq → ∀ t : ℝ, 0 < t →
      ∀ T : Finset (Torus d n), ((t ≤ n) ∨ (0 : Torus d n) ∉ T) →
      ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, (P.P t).eval (uhat msq m) * Real.sqrt (lam m) ^ A ≤
        C * (1 + t ^ 2 * (msq / (2 * d + msq))) ^ (-s) * ((1 + t) ^ (d + A))⁻¹ := by
  obtain ⟨K, hK0, hK⟩ := eval_uhat_le P hd hs (A + d)
  set B := Real.sqrt (4 * d)
  set Cd : ℝ := ((d + 4) / 4 : ℝ) ^ d * (1 + Real.pi * d) ^ d
  have hCd1 : (1 + Real.pi * d) ^ d ≤ Cd := by
    refine le_mul_of_one_le_left (by positivity) (one_le_pow₀ ?_)
    rw [le_div_iff₀ (by norm_num)]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hCd0 : 0 ≤ Cd := by positivity
  refine ⟨K * B ^ A * 2 ^ (d + A) * Cd + K * B ^ A * 2 ^ (d + A), by positivity,
    fun n _ msq hmsq t ht T hT => ?_⟩
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (NeZero.pos n)
  set R := (1 + t ^ 2 * (msq / (2 * d + msq))) ^ (-s)
  have hR : 0 ≤ R := by positivity
  set Y : Torus d n → ℝ := fun m => ((1 + t ^ 2 * lam m / (4 * d)) ^ (A + d))⁻¹
  have hterm : ∀ m, (P.P t).eval (uhat msq m) * Real.sqrt (lam m) ^ A ≤
      K * R * (Real.sqrt (lam m) ^ A * Y m) := by
    intro m
    have h1 := hK n msq hmsq t ht m
    have h0 := P.nonneg t ht _ (uhat_mem hmsq m)
    calc (P.P t).eval (uhat msq m) * Real.sqrt (lam m) ^ A
        ≤ (K * R * Y m) * Real.sqrt (lam m) ^ A := by gcongr
      _ = _ := by ring
  have hsum : ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, (P.P t).eval (uhat msq m) * Real.sqrt (lam m) ^ A ≤
      K * R * (((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, Real.sqrt (lam m) ^ A * Y m) := by
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_le_sum fun m _ => ?_
    have := hterm m
    calc ((n : ℝ) ^ d)⁻¹ * ((P.P t).eval (uhat msq m) * Real.sqrt (lam m) ^ A)
        ≤ ((n : ℝ) ^ d)⁻¹ * (K * R * (Real.sqrt (lam m) ^ A * Y m)) := by gcongr
      _ = _ := by ring
  refine hsum.trans ?_
  have hT0 : ∀ m, 0 ≤ Real.sqrt (lam m) ^ A * Y m := fun m => by
    have := lam_nonneg m; positivity
  rcases lt_or_ge t 1 with ht1 | ht1
  · -- small `t`: trivial bound
    have h1 : ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, Real.sqrt (lam m) ^ A * Y m ≤ B ^ A := by
      calc ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, Real.sqrt (lam m) ^ A * Y m
          ≤ ((n : ℝ) ^ d)⁻¹ * ∑ m : Torus d n, B ^ A := by
            gcongr
            exact (sum_le_sum_of_subset_of_nonneg (subset_univ T) fun m _ _ => hT0 m).trans
              (sum_le_sum fun m _ => sqrt_pow_mul_le' A (A + d) m)
        _ = B ^ A := by
            rw [sum_const, card_univ, card_torus, nsmul_eq_mul]; push_cast; field_simp
    have h2 : 1 ≤ 2 ^ (d + A) * ((1 + t) ^ (d + A))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    calc K * R * (((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, Real.sqrt (lam m) ^ A * Y m)
        ≤ K * R * B ^ A := by gcongr
      _ ≤ K * R * B ^ A * (2 ^ (d + A) * ((1 + t) ^ (d + A))⁻¹) := le_mul_of_one_le_right
          (by positivity) h2
      _ ≤ (K * B ^ A * 2 ^ (d + A) * Cd + K * B ^ A * 2 ^ (d + A)) * R *
            ((1 + t) ^ (d + A))⁻¹ := by
          have : 0 ≤ K * B ^ A * 2 ^ (d + A) * Cd * R * ((1 + t) ^ (d + A))⁻¹ := by positivity
          nlinarith
  · -- large `t`: lattice sums
    have ht0 : 0 < t := ht
    have hlat : ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹ ≤ Cd / t ^ d := by
      have hnn : ∀ m : Torus d n, 0 ≤ ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹ := fun m => by
        have := lam_nonneg m; positivity
      rcases hT with htn | h0
      · calc ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹
            ≤ ((n : ℝ) ^ d)⁻¹ * ∑ m : Torus d n, ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹ := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact sum_le_sum_of_subset_of_nonneg (subset_univ T) fun m _ _ => hnn m
          _ ≤ (1 + Real.pi * d) ^ d / t ^ d := latt_small hd ht1 htn
          _ ≤ Cd / t ^ d := by gcongr
      · rcases le_or_gt t n with htn | htn
        · calc ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹
              ≤ ((n : ℝ) ^ d)⁻¹ * ∑ m : Torus d n, ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹ := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact sum_le_sum_of_subset_of_nonneg (subset_univ T) fun m _ _ => hnn m
            _ ≤ (1 + Real.pi * d) ^ d / t ^ d := latt_small hd ht1 htn
            _ ≤ Cd / t ^ d := by gcongr
        · calc ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹
              ≤ ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ univ.erase (0 : Torus d n),
                  ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹ := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                refine sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hnn m
                intro m hm; exact mem_erase.2 ⟨fun h => h0 (h ▸ hm), mem_univ m⟩
            _ ≤ Cd / t ^ d := latt_large hd htn.le
    have h1 : ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, Real.sqrt (lam m) ^ A * Y m ≤
        (B / t) ^ A * (Cd / t ^ d) := by
      calc ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, Real.sqrt (lam m) ^ A * Y m
          ≤ ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, (B / t) ^ A * ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹ := by
            refine mul_le_mul_of_nonneg_left (sum_le_sum fun m _ => ?_) (by positivity)
            exact sqrt_pow_mul_le hd A ht0 (lam_nonneg m)
        _ = (B / t) ^ A * (((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, ((1 + t ^ 2 * lam m / (4 * d)) ^ d)⁻¹) := by
            rw [← mul_sum]; ring
        _ ≤ (B / t) ^ A * (Cd / t ^ d) := by gcongr
    have h2 : (B / t) ^ A * (Cd / t ^ d) ≤ B ^ A * 2 ^ (d + A) * Cd * ((1 + t) ^ (d + A))⁻¹ := by
      have e : (B / t) ^ A * (Cd / t ^ d) = B ^ A * Cd * (t ^ (d + A))⁻¹ := by
        rw [div_pow, pow_add]; field_simp
      rw [e]
      have h3 : (t ^ (d + A))⁻¹ ≤ 2 ^ (d + A) * ((1 + t) ^ (d + A))⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, ← div_pow]
        exact pow_le_pow_left₀ (by positivity) (by rw [div_le_iff₀ ht0]; linarith) _
      calc B ^ A * Cd * (t ^ (d + A))⁻¹ ≤ B ^ A * Cd * (2 ^ (d + A) * ((1 + t) ^ (d + A))⁻¹) := by
            gcongr
        _ = _ := by ring
    calc K * R * (((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, Real.sqrt (lam m) ^ A * Y m)
        ≤ K * R * (B ^ A * 2 ^ (d + A) * Cd * ((1 + t) ^ (d + A))⁻¹) := by
          exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ ≤ (K * B ^ A * 2 ^ (d + A) * Cd + K * B ^ A * 2 ^ (d + A)) * R *
            ((1 + t) ^ (d + A))⁻¹ := by
          have : 0 ≤ K * B ^ A * 2 ^ (d + A) * R * ((1 + t) ^ (d + A))⁻¹ := by positivity
          nlinarith

/-! ### Integrating over the scales -/

theorem sum_wt_mul {msq : ℝ} {S : Set ℝ} (T : Finset (Torus d n)) (g : Torus d n → ℝ)
    (hint : ∀ m ∈ T, IntegrableOn (fun t => t * (P.P t).eval (uhat msq m)) S) :
    ∑ m ∈ T, wt P msq S m * g m =
      (2 * d + msq)⁻¹ * ∫ t in S, ∑ m ∈ T, t * (P.P t).eval (uhat msq m) * g m := by
  rw [integral_finsetSum _ fun m hm => (hint m hm).mul_const _, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [wt, integral_mul_const]; ring

/-- The bound for a fixed order `A` and general scales `S ⊆ (a, ∞)`. -/
theorem core_bound (hd : 3 ≤ d) {s : ℝ} (hs : 0 ≤ s) (A : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) [NeZero n] (msq : ℝ), 0 ≤ msq → ∀ a : ℝ, 0 ≤ a →
      ∀ S : Set ℝ, MeasurableSet S → S ⊆ Ioi a → ∀ T : Finset (Torus d n),
      (∀ t ∈ S, t ≤ n ∨ (0 : Torus d n) ∉ T) →
      (∀ m ∈ T, IntegrableOn (fun t => t * (P.P t).eval (uhat msq m)) S) →
      ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, wt P msq S m * Real.sqrt (lam m) ^ A ≤
        K * ((2 * d + msq)⁻¹ * (1 + a ^ 2 * (msq / (2 * d + msq))) ^ (-s)) *
          ((1 + a) ^ (d + A - 2))⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := psi_bound P (by omega : 1 ≤ d) hs A
  set r := d + A - 2 with hr
  have hr1 : 1 ≤ r := by omega
  have hrD : d + A = r + 1 + 1 := by omega
  refine ⟨C / r, by positivity, fun n _ msq hmsq a ha S hS hSa T hT hint => ?_⟩
  have hc : (0 : ℝ) < 2 * d + msq := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set ρ := msq / (2 * d + msq)
  have hρ : 0 ≤ ρ := by positivity
  set F : ℝ → ℝ := fun t => ((n : ℝ) ^ d)⁻¹ *
    ∑ m ∈ T, t * (P.P t).eval (uhat msq m) * Real.sqrt (lam m) ^ A
  set G : ℝ → ℝ := fun t => C * (1 + a ^ 2 * ρ) ^ (-s) * ((1 + t) ^ (r + 1))⁻¹
  have hLHS : ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, wt P msq S m * Real.sqrt (lam m) ^ A =
      (2 * d + msq)⁻¹ * ∫ t in S, F t := by
    rw [sum_wt_mul P T _ hint, integral_const_mul]; ring
  have hGi : IntegrableOn G (Ioi a) := (integrableOn_inv_pow hr1 ha).const_mul _
  have hFG : ∀ t ∈ S, 0 ≤ F t ∧ F t ≤ G t := by
    intro t htS
    have hta : a < t := hSa htS
    have ht0 : 0 < t := lt_of_le_of_lt ha hta
    have hF : F t = t * (((n : ℝ) ^ d)⁻¹ *
        ∑ m ∈ T, (P.P t).eval (uhat msq m) * Real.sqrt (lam m) ^ A) := by
      simp only [F, mul_sum]; refine sum_congr rfl fun m _ => by ring
    have hnn : 0 ≤ ((n : ℝ) ^ d)⁻¹ *
        ∑ m ∈ T, (P.P t).eval (uhat msq m) * Real.sqrt (lam m) ^ A :=
      mul_nonneg (by positivity) (sum_nonneg fun m _ =>
        mul_nonneg (P.nonneg t ht0 _ (uhat_mem hmsq m)) (by positivity))
    refine ⟨by rw [hF]; exact mul_nonneg ht0.le hnn, ?_⟩
    rw [hF]
    have h1 := hC n msq hmsq t ht0 T (hT t htS)
    have h2 : (1 + t ^ 2 * ρ) ^ (-s) ≤ (1 + a ^ 2 * ρ) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by positivity)
        (by gcongr) (by linarith)
    have h3 : t * ((1 + t) ^ (d + A))⁻¹ ≤ ((1 + t) ^ (r + 1))⁻¹ := by
      rw [hrD, pow_succ, mul_inv, ← mul_assoc, mul_comm t, mul_assoc]
      refine mul_le_of_le_one_right (by positivity) ?_
      rw [← div_eq_mul_inv, div_le_one (by positivity)]; linarith
    calc t * (((n : ℝ) ^ d)⁻¹ * ∑ m ∈ T, (P.P t).eval (uhat msq m) * Real.sqrt (lam m) ^ A)
        ≤ t * (C * (1 + t ^ 2 * ρ) ^ (-s) * ((1 + t) ^ (d + A))⁻¹) :=
          mul_le_mul_of_nonneg_left h1 ht0.le
      _ = C * (1 + t ^ 2 * ρ) ^ (-s) * (t * ((1 + t) ^ (d + A))⁻¹) := by ring
      _ ≤ C * (1 + a ^ 2 * ρ) ^ (-s) * ((1 + t) ^ (r + 1))⁻¹ := by
          gcongr
  have hint1 : ∫ t in S, F t ≤ ∫ t in S, G t := by
    refine integral_mono_of_nonneg ?_ (hGi.mono_set hSa) ?_
    · exact (ae_restrict_iff' hS).2 (Eventually.of_forall fun t ht => (hFG t ht).1)
    · exact (ae_restrict_iff' hS).2 (Eventually.of_forall fun t ht => (hFG t ht).2)
  have hint2 : ∫ t in S, G t ≤ ∫ t in Ioi a, G t := by
    refine setIntegral_mono_set hGi ?_ (Eventually.of_forall hSa)
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have : 0 ≤ t := ha.trans (le_of_lt ht)
    simp only [G]; positivity
  have hint3 : ∫ t in Ioi a, G t = C * (1 + a ^ 2 * ρ) ^ (-s) * (((1 + a) ^ r)⁻¹ / r) := by
    simp only [G]; rw [integral_const_mul, integral_inv_pow hr1 ha]
  rw [hLHS]
  calc (2 * d + msq)⁻¹ * ∫ t in S, F t
      ≤ (2 * d + msq)⁻¹ * (C * (1 + a ^ 2 * ρ) ^ (-s) * (((1 + a) ^ r)⁻¹ / r)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← hint3]; exact hint1.trans hint2
    _ = _ := by ring

/-! ### The factors `ϑ_j` and `L^{-(d-2+A)j}` -/

theorem rho_factor {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) {L : ℝ} (hL : 1 ≤ L) (j : ℕ)
    {msq : ℝ} (hmsq : 0 ≤ msq) :
    (1 + lowEnd L (j + 1) ^ 2 * (msq / (2 * d + msq))) ^ (-s) ≤
      4 ^ s * (1 + msq * L ^ (2 * j) / (2 * d + msq)) ^ (-s) := by
  have hc : (0 : ℝ) < 2 * d + msq := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set x := msq * L ^ (2 * j) / (2 * d + msq)
  have hx : 0 ≤ x := by have : 0 ≤ L := by linarith
                        positivity
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hlow : lowEnd L (0 + 1) = 0 := by simp [lowEnd]
    rw [hlow]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero,
      Real.one_rpow]
    have hx1 : x ≤ 1 := by
      simp only [x, mul_zero, pow_zero, mul_one]
      rw [div_le_one hc]
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    calc (1 + x) ^ s ≤ 2 ^ s := Real.rpow_le_rpow (by positivity) (by linarith) hs
      _ ≤ 4 ^ s := Real.rpow_le_rpow (by norm_num) (by norm_num) hs
  · rw [lowEnd_succ L hj]
    have e : 1 + (L ^ j / 2) ^ 2 * (msq / (2 * d + msq)) = 1 + x / 4 := by
      simp only [x]; rw [pow_mul]; field_simp; ring
    rw [e]
    have h1 : (1 + x) / 4 ≤ 1 + x / 4 := by linarith
    calc (1 + x / 4) ^ (-s) ≤ ((1 + x) / 4) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
      _ = 4 ^ s * (1 + x) ^ (-s) := by
          rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
          field_simp

theorem len_factor {L : ℝ} (hL : 1 ≤ L) (j r : ℕ) :
    ((1 + lowEnd L (j + 1)) ^ r)⁻¹ ≤ 2 ^ r * L ^ (-((r : ℝ) * j)) := by
  have hL0 : 0 < L := by linarith
  have e : L ^ (-((r : ℝ) * j)) = ((L ^ j) ^ r)⁻¹ := by
    rw [Real.rpow_neg hL0.le, show (r : ℝ) * j = ((j * r : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul]
  rw [e]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hlow : lowEnd L (0 + 1) = 0 := by simp [lowEnd]
    rw [hlow]; simp only [add_zero, one_pow, inv_one, pow_zero, mul_one]
    exact one_le_pow₀ (by norm_num)
  · rw [lowEnd_succ L hj]
    have h1 : L ^ j / 2 ≤ 1 + L ^ j / 2 := by linarith
    calc ((1 + L ^ j / 2) ^ r)⁻¹ ≤ ((L ^ j / 2) ^ r)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 r)
      _ = 2 ^ r * ((L ^ j) ^ r)⁻¹ := by rw [div_pow]; field_simp

/-! ### `e:C-bd` for a fixed order `A = |α_1| + |α_2|` -/

theorem exponent_eq {d : ℕ} (hd : 3 ≤ d) (α₁ α₂ : Dir d → ℕ) :
    (((d + (mabs α₁ + mabs α₂) - 2 : ℕ) : ℝ)) = (d : ℝ) - 2 + mabs α₁ + mabs α₂ := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

theorem Cj_bound_fixed (hd : 3 ≤ d) {s : ℝ} (hs : 0 ≤ s) (A : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) [NeZero n] (L : ℝ), 1 ≤ L → ∀ j : ℕ, L ^ (j + 1) ≤ n →
      ∀ msq : ℝ, 0 ≤ msq → ∀ α₁ α₂ : Dir d → ℕ, mabs α₁ + mabs α₂ = A → ∀ x y : Torus d n,
      |nabC (Cj P msq L (j + 1) : Matrix (Torus d n) (Torus d n) ℝ) α₁ α₂ x y| ≤
        K * ((2 * d + msq)⁻¹ * (1 + msq * L ^ (2 * j) / (2 * d + msq)) ^ (-s)) *
          L ^ (-(((d : ℝ) - 2 + mabs α₁ + mabs α₂) * j)) := by
  obtain ⟨K, hK0, hK⟩ := core_bound P hd hs A
  refine ⟨K * 4 ^ s * 2 ^ (d + A - 2), by positivity,
    fun n _ L hL j hjn msq hmsq α₁ α₂ hA x y => ?_⟩
  have hL0 : 0 ≤ L := by linarith
  set a := lowEnd L (j + 1)
  have ha : 0 ≤ a := lowEnd_nonneg hL0 _
  set S := Ioc a (L ^ (j + 1) / 2)
  have hc : (0 : ℝ) < 2 * d + msq := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h1 := abs_nabC_fmat_le (wt P msq S) α₁ α₂ x y
  have hw : ∀ m : Torus d n, |wt P msq S m| = wt P msq S m := fun m =>
    abs_of_nonneg (wt_nonneg P hmsq measurableSet_Ioc (fun t ht => lt_of_le_of_lt ha ht.1) m)
  simp only [hw, hA] at h1
  have h2 := hK n msq hmsq a ha S measurableSet_Ioc Ioc_subset_Ioi_self univ
    (fun t ht => Or.inl (by
      have : t ≤ L ^ (j + 1) / 2 := ht.2
      have : 0 ≤ L ^ (j + 1) := by positivity
      linarith))
    (fun m _ => integrableOn_Ioc P (uhat_mem hmsq m) _ ha)
  have h3 := rho_factor (by omega : 1 ≤ d) hs hL j hmsq
  have h4 := len_factor hL j (d + A - 2)
  have hex : ((d + A - 2 : ℕ) : ℝ) = (d : ℝ) - 2 + mabs α₁ + mabs α₂ := by
    rw [← hA]; exact exponent_eq hd α₁ α₂
  rw [hex] at h4
  have e : (Cj P msq L (j + 1) : Matrix (Torus d n) (Torus d n) ℝ) = fmat (wt P msq S) := rfl
  rw [e]
  calc |nabC (fmat (wt P msq S)) α₁ α₂ x y|
      ≤ ((n : ℝ) ^ d)⁻¹ * ∑ m, wt P msq S m * Real.sqrt (lam m) ^ A := h1
    _ ≤ K * ((2 * d + msq)⁻¹ * (1 + a ^ 2 * (msq / (2 * d + msq))) ^ (-s)) *
          ((1 + a) ^ (d + A - 2))⁻¹ := h2
    _ ≤ K * ((2 * d + msq)⁻¹ * (4 ^ s * (1 + msq * L ^ (2 * j) / (2 * d + msq)) ^ (-s))) *
          (2 ^ (d + A - 2) * L ^ (-(((d : ℝ) - 2 + mabs α₁ + mabs α₂) * j))) := by
        gcongr
    _ = _ := by ring

theorem CN_bound_fixed (hd : 3 ≤ d) {s : ℝ} (hs : 0 ≤ s) (A : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L : ℕ) [NeZero L], 1 ≤ L → ∀ N : ℕ, 1 ≤ N → ∀ msq : ℝ, 0 ≤ msq →
      ∀ α₁ α₂ : Dir d → ℕ, mabs α₁ + mabs α₂ = A → ∀ x y : Torus d (L ^ N),
      |nabC (CN P msq L N : Matrix (Torus d (L ^ N)) (Torus d (L ^ N)) ℝ) α₁ α₂ x y| ≤
        K * ((2 * d + msq)⁻¹ * (1 + msq * (L : ℝ) ^ (2 * (N - 1)) / (2 * d + msq)) ^ (-s)) *
          (L : ℝ) ^ (-(((d : ℝ) - 2 + mabs α₁ + mabs α₂) * (N - 1 : ℕ))) := by
  obtain ⟨K, hK0, hK⟩ := core_bound P hd hs A
  refine ⟨K * 4 ^ s * 2 ^ (d + A - 2), by positivity,
    fun L _ hL1 N hN msq hmsq α₁ α₂ hA x y => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hL0 : (0 : ℝ) ≤ L := by linarith
  set a := lowEnd (L : ℝ) (j + 1)
  have ha : 0 ≤ a := lowEnd_nonneg hL0 _
  set S := Ioi a
  have hc : (0 : ℝ) < 2 * d + msq := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set w : Torus d (L ^ (j + 1)) → ℝ := fun m => if m = 0 then 0 else wt P msq S m
  have h1 := abs_nabC_fmat_le w α₁ α₂ x y
  have hsum : ∑ m, |w m| * Real.sqrt (lam m) ^ (mabs α₁ + mabs α₂) =
      ∑ m ∈ univ.erase (0 : Torus d (L ^ (j + 1))), wt P msq S m * Real.sqrt (lam m) ^ A := by
    rw [← Finset.add_sum_erase univ _ (mem_univ (0 : Torus d (L ^ (j + 1))))]
    simp only [w, if_pos rfl, abs_zero, zero_mul, zero_add, hA]
    refine sum_congr rfl fun m hm => ?_
    rw [if_neg (mem_erase.1 hm).1, abs_of_nonneg
      (wt_nonneg P hmsq measurableSet_Ioi (fun t ht => lt_of_le_of_lt ha ht) m)]
  rw [hsum] at h1
  have hint : ∀ m ∈ univ.erase (0 : Torus d (L ^ (j + 1))),
      IntegrableOn (fun t => t * (P.P t).eval (uhat msq m)) S := by
    intro m hm
    have hm0 : m ≠ 0 := (mem_erase.1 hm).1
    have hlam : 0 < lam m := by
      have h1 := lam_ge m
      have h2 := one_le_sum_zabs_sq hm0
      have hn : (0 : ℝ) < ((L ^ (j + 1) : ℕ) : ℝ) := Nat.cast_pos.2 (NeZero.pos _)
      have : 0 < 16 / (((L ^ (j + 1) : ℕ) : ℝ)) ^ 2 := by positivity
      nlinarith
    have hu : uhat msq m ∈ Ioc (0 : ℝ) 2 :=
      ⟨div_pos (by linarith) hc, (uhat_mem hmsq m).2⟩
    exact integrableOn_Ioi P hu ha
  have h2 := hK (L ^ (j + 1)) msq hmsq a ha S measurableSet_Ioi (fun _ h => h) (univ.erase 0)
    (fun t _ => Or.inr (fun h => (mem_erase.1 h).1 rfl)) hint
  have h3 := rho_factor (by omega : 1 ≤ d) hs hL j hmsq
  have h4 := len_factor hL j (d + A - 2)
  have hex : ((d + A - 2 : ℕ) : ℝ) = (d : ℝ) - 2 + mabs α₁ + mabs α₂ := by
    rw [← hA]; exact exponent_eq hd α₁ α₂
  rw [hex] at h4
  have e : (CN P msq L (j + 1) : Matrix (Torus d (L ^ (j + 1))) (Torus d (L ^ (j + 1))) ℝ) =
    fmat w := rfl
  rw [e]
  calc |nabC (fmat w) α₁ α₂ x y|
      ≤ (((L ^ (j + 1) : ℕ) : ℝ) ^ d)⁻¹ *
          ∑ m ∈ univ.erase 0, wt P msq S m * Real.sqrt (lam m) ^ A := h1
    _ ≤ K * ((2 * d + msq)⁻¹ * (1 + a ^ 2 * (msq / (2 * d + msq))) ^ (-s)) *
          ((1 + a) ^ (d + A - 2))⁻¹ := h2
    _ ≤ K * ((2 * d + msq)⁻¹ * (4 ^ s * (1 + msq * (L : ℝ) ^ (2 * j) / (2 * d + msq)) ^ (-s))) *
          (2 ^ (d + A - 2) * (L : ℝ) ^ (-(((d : ℝ) - 2 + mabs α₁ + mabs α₂) * j))) := by
        gcongr
    _ = _ := by ring

/-! ### `e:C-bd` -/

theorem uniform_of_fixed {p : ℕ} {Q : ℕ → ℝ → Prop}
    (hmono : ∀ A K K', K ≤ K' → Q A K → Q A K')
    (h : ∀ A, ∃ K : ℝ, 0 ≤ K ∧ Q A K) : ∃ K : ℝ, ∀ A ≤ 2 * p, Q A K := by
  choose K hK0 hK using h
  refine ⟨∑ A ∈ range (2 * p + 1), K A, fun A hA => hmono A _ _ ?_ (hK A)⟩
  exact single_le_sum (f := K) (fun A _ => hK0 A) (mem_range.2 (by omega))

/-- `e:C-bd` for `C_{j+1}`, `j + 1 < N` (uniform in the torus as long as `L^{j+1} ≤ n`). -/
theorem Cj_bound (hd : 3 ≤ d) (s : ℝ) (hs : 0 ≤ s) (p : ℕ) :
    ∃ K : ℝ, ∀ (n : ℕ) [NeZero n] (L : ℝ), 1 ≤ L → ∀ j : ℕ, L ^ (j + 1) ≤ n → ∀ msq : ℝ, 0 ≤ msq →
      ∀ α₁ α₂ : Dir d → ℕ, mabs α₁ ≤ p → mabs α₂ ≤ p → ∀ x y : Torus d n,
      |nabC (Cj P msq L (j + 1) : Matrix (Torus d n) (Torus d n) ℝ) α₁ α₂ x y| ≤
        K * ((2 * d + msq)⁻¹ * (1 + msq * L ^ (2 * j) / (2 * d + msq)) ^ (-s)) *
          L ^ (-(((d : ℝ) - 2 + mabs α₁ + mabs α₂) * j)) := by
  obtain ⟨K, hK⟩ := uniform_of_fixed (p := p)
    (Q := fun A K => ∀ (n : ℕ) [NeZero n] (L : ℝ), 1 ≤ L → ∀ j : ℕ, L ^ (j + 1) ≤ n →
      ∀ msq : ℝ, 0 ≤ msq → ∀ α₁ α₂ : Dir d → ℕ, mabs α₁ + mabs α₂ = A → ∀ x y : Torus d n,
      |nabC (Cj P msq L (j + 1) : Matrix (Torus d n) (Torus d n) ℝ) α₁ α₂ x y| ≤
        K * ((2 * d + msq)⁻¹ * (1 + msq * L ^ (2 * j) / (2 * d + msq)) ^ (-s)) *
          L ^ (-(((d : ℝ) - 2 + mabs α₁ + mabs α₂) * j)))
    (fun A K K' hKK' hQ n _ L hL j hj msq hmsq α₁ α₂ hA x y => by
      refine (hQ n L hL j hj msq hmsq α₁ α₂ hA x y).trans ?_
      have hc : (0 : ℝ) < 2 * d + msq := by
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have : 0 ≤ L := by linarith
      gcongr)
    (fun A => Cj_bound_fixed P hd hs A)
  exact ⟨K, fun n _ L hL j hj msq hmsq α₁ α₂ h₁ h₂ x y =>
    hK _ (by omega) n L hL j hj msq hmsq α₁ α₂ rfl x y⟩

/-- The bounded part `C_N` of the last covariance satisfies `e:C-bd` with `j + 1 = N`,
`n = L^N`. -/
theorem CN_bound (hd : 3 ≤ d) (s : ℝ) (hs : 0 ≤ s) (p : ℕ) :
    ∃ K : ℝ, ∀ (L : ℕ) [NeZero L], 1 ≤ L → ∀ N : ℕ, 1 ≤ N → ∀ msq : ℝ, 0 ≤ msq →
      ∀ α₁ α₂ : Dir d → ℕ, mabs α₁ ≤ p → mabs α₂ ≤ p → ∀ x y : Torus d (L ^ N),
      |nabC (CN P msq L N : Matrix (Torus d (L ^ N)) (Torus d (L ^ N)) ℝ) α₁ α₂ x y| ≤
        K * ((2 * d + msq)⁻¹ * (1 + msq * (L : ℝ) ^ (2 * (N - 1)) / (2 * d + msq)) ^ (-s)) *
          (L : ℝ) ^ (-(((d : ℝ) - 2 + mabs α₁ + mabs α₂) * (N - 1 : ℕ))) := by
  obtain ⟨K, hK⟩ := uniform_of_fixed (p := p)
    (Q := fun A K => ∀ (L : ℕ) [NeZero L], 1 ≤ L → ∀ N : ℕ, 1 ≤ N → ∀ msq : ℝ, 0 ≤ msq →
      ∀ α₁ α₂ : Dir d → ℕ, mabs α₁ + mabs α₂ = A → ∀ x y : Torus d (L ^ N),
      |nabC (CN P msq L N : Matrix (Torus d (L ^ N)) (Torus d (L ^ N)) ℝ) α₁ α₂ x y| ≤
        K * ((2 * d + msq)⁻¹ * (1 + msq * (L : ℝ) ^ (2 * (N - 1)) / (2 * d + msq)) ^ (-s)) *
          (L : ℝ) ^ (-(((d : ℝ) - 2 + mabs α₁ + mabs α₂) * (N - 1 : ℕ))))
    (fun A K K' hKK' hQ L _ hL N hN msq hmsq α₁ α₂ hA x y => by
      refine (hQ L hL N hN msq hmsq α₁ α₂ hA x y).trans ?_
      have hc : (0 : ℝ) < 2 * d + msq := by
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      gcongr)
    (fun A => CN_bound_fixed P hd hs A)
  exact ⟨K, fun L _ hL N hN msq hmsq α₁ α₂ h₁ h₂ x y =>
    hK _ (by omega) L hL N hN msq hmsq α₁ α₂ rfl x y⟩

end

end FRD
