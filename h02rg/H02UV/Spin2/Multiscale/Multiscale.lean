import Spin2.Multiscale.Conn
import Spin2.Multiscale.BetaThm
import Obs.Norm

/-!
# Expected result `thm:multiscale` from `thm:rginput` and (H_λ)

`h02uv-outline.tex`, Expected result 1.2: uniformly in `ε ≤ |x| ≤ 1/2`,
`P_ε(x) = ϑ²_{j(|x|)}(1 + O(β_{j(|x|)}^{-1}))`, `ϑ_j² = (β_j/β_ε)^{2/3}(1 + O(β_j^{-1}))`,
`j(ℓ) = ⌊N + log_L ℓ⌋`.

Objects (lattice units, `ε = L^{-N}`, `𝕋_ε ≅ Λ_N = Lam 2 L N`, the point `x_ε` is `x : Λ_N`):
* `Pconn L N β x = P_β[0 ↔ x]` (`Spin2/Multiscale/Conn.lean`), `β_ε = 1/b`;
* `eucl x`: the Euclidean torus distance `|x|` in lattice units, so the physical distance is
  `ℓ = eucl x / L^N`, and `jPhys L N ℓ = ⌊N + log_L ℓ⌋`;
* the coalescence scale `j_x = Obs.coal L 0 x = ⌊log_L(2|x|_∞)⌋` (the `j_ab` of `Obs2`,
  `Obs2.obsHist_coal`);
* along a trajectory `t = traj (rgDataM R m) L² b μ₀`: `ǧ_k = (t k).1`, `β_k = betaJ = 1/ǧ_k`,
  `ϑ_k² = thetaSq = (β_k/β_ε)^{2/3}`, and `M_j = Mmag = 1 - b∑_{k<j} λ̂_kΓ^int_{k+1}(0,0)`
  (`e:PM`) for a vertex sequence `λ̂`.

Named hypotheses (the remaining targets):
* `HLam` = (H_λ): `‖λ̂_k - (ǧ_k/b)^{1/3}‖ ≤ K_λ(ǧ_k/b)^{1/3}(ǧ_k + a_k)` for `k < N_h`;
* `RGInput` = `thm:rginput`: for `x ≠ 0` with `j_x ≤ N_h`,
  `‖P_{1/b}[0 ↔ x] - M_{j_x}²‖ ≤ K_P‖M_{j_x}‖²ǧ_{j_x}`.

Results:
* `coal_jPhys`: `j(|x|) ∈ {j_x - 1, j_x}` for `x ≠ 0`, `L ≥ 2`;
* `multi_core`, `multi_shift` (pure);
* `MultiConcl`, `multiConcl_of`: from `SpinConcl` and `MagConcl` (same constants), along every
  admissible trajectory, (H_λ) and `RGInput` give `|P - ϑ²_{j(|x|)}| ≤ K ϑ²_{j(|x|)}/β_{j(|x|)}`
  for `x ≠ 0`, `j_x ≤ N_h`, with `K = multK` depending on `L`, the flow constants, `K_λ`, `K_P`;
* `MultiConclR`: the same at `β_ε = 1/bFin(m², 1/β_R)` (`thm:beta`);
* **`thm_multiscale`**: one set of constants with `thm:flow`, `thm:beta` and `MultiConclR`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L N : ℕ} [NeZero L]

/-! ## Physical scale vs coalescence scale -/

/-- The Euclidean torus distance `|x|` (lattice units) on `Λ_N`. -/
def eucl (x : Lam 2 L N) : ℝ :=
  Real.sqrt (∑ i, ((zabs ((x : Fin 2 → ZMod (L ^ N)) i) : ℕ) : ℝ) ^ 2)

variable (L N) in
/-- `j(ℓ) = ⌊N + log_L ℓ⌋`, the scale of a physical length `ℓ`. -/
def jPhys (ℓ : ℝ) : ℤ := ⌊(N : ℝ) + Real.logb L ℓ⌋

omit [NeZero L] in
theorem supNorm_le_eucl (x : Lam 2 L N) : (supNorm x : ℝ) ≤ eucl x := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin 2)) univ_nonempty
    (fun i => zabs ((x : Fin 2 → ZMod (L ^ N)) i))
  rw [eucl, supNorm, hi]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun i => ((zabs ((x : Fin 2 → ZMod (L ^ N)) i) : ℕ) : ℝ) ^ 2)
    (fun _ _ => sq_nonneg _) (mem_univ i)

omit [NeZero L] in
theorem eucl_le_two_supNorm (x : Lam 2 L N) : eucl x ≤ 2 * (supNorm x : ℝ) := by
  rw [eucl, Real.sqrt_le_left (by positivity)]
  have h : ∀ i, ((zabs ((x : Fin 2 → ZMod (L ^ N)) i) : ℕ) : ℝ) ^ 2 ≤ (supNorm x : ℝ) ^ 2 := by
    intro i
    have : zabs ((x : Fin 2 → ZMod (L ^ N)) i) ≤ supNorm x :=
      Finset.le_sup (f := fun i => zabs ((x : Fin 2 → ZMod (L ^ N)) i)) (mem_univ i)
    have : ((zabs ((x : Fin 2 → ZMod (L ^ N)) i) : ℕ) : ℝ) ≤ supNorm x := by exact_mod_cast this
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  rw [Fin.sum_univ_two]
  nlinarith [h 0, h 1, sq_nonneg (supNorm x : ℝ)]

/-- **`j(|x|)` vs the coalescence scale**: for `x ≠ 0` and `L ≥ 2`, with `ℓ = |x|/L^N` (physical
units), `j(ℓ) ∈ {j_x - 1, j_x}`, `j_x = Obs.coal L 0 x`. -/
theorem coal_jPhys (hL : 2 ≤ L) {x : Lam 2 L N} (hx : x ≠ 0) :
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧ jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧
      Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 := by
  have hs : Obs.coal L (0 : Lam 2 L N) x = Nat.log L (2 * supNorm x) := by
    rw [Obs.coal, zero_sub, supNorm_neg]
  set s := supNorm x with hsd
  set j := Nat.log L (2 * s) with hjd
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · exact absurd ((FRD.supNorm_eq_zero_iff x).1 h0) hx
    · exact h0
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have he1 : (1 : ℝ) ≤ eucl x := le_trans (by exact_mod_cast hs1) (supNorm_le_eucl x)
  have he0 : 0 < eucl x := by linarith
  have hlog : (N : ℝ) + Real.logb L (eucl x / (L : ℝ) ^ N) = Real.logb L (eucl x) := by
    rw [Real.logb_div he0.ne' (pow_pos hL0 N).ne', Real.logb_pow, Real.logb_self_eq_one hL1]
    ring
  set y := Real.logb L (eucl x) with hyd
  have hy0 : 0 ≤ y := Real.logb_nonneg hL1 he1
  -- upper: `|x| ≤ 2|x|_∞ < L^{j+1}`
  have hup : y < ((j + 1 : ℕ) : ℝ) := by
    rw [hyd, Real.logb_lt_iff_lt_rpow hL1 he0, Real.rpow_natCast]
    have h1 : 2 * s < L ^ (j + 1) := Nat.lt_pow_succ_log_self (by omega) _
    have h2 : ((2 * s : ℕ) : ℝ) < ((L ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith [supNorm_le_eucl x, eucl_le_two_supNorm x]
  -- lower: `L^{j-1} ≤ L^j/2 ≤ |x|_∞ ≤ |x|`
  have hlow : ((j - 1 : ℕ) : ℝ) ≤ y := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0]; simpa using hy0
    rw [hyd, Real.le_logb_iff_rpow_le hL1 he0, Real.rpow_natCast]
    have h1 : L ^ j ≤ 2 * s := Nat.pow_log_le_self L (by omega)
    have h2 : ((L ^ j : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have h3 : (L : ℝ) ^ j = L * (L : ℝ) ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h4 : (0 : ℝ) ≤ (L : ℝ) ^ (j - 1) := by positivity
    have h5 : (2 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith [supNorm_le_eucl x]
  refine ⟨(⌊y⌋).toNat, ?_, ?_, ?_⟩
  · rw [jPhys, hlog, Int.toNat_of_nonneg (Int.floor_nonneg.2 hy0)]
  · rw [hs]
    have : ⌊y⌋ < ((j + 1 : ℕ) : ℤ) := Int.floor_lt.2 (by exact_mod_cast hup)
    omega
  · rw [hs]
    have : ((j - 1 : ℕ) : ℤ) ≤ ⌊y⌋ := Int.le_floor.2 (by exact_mod_cast hlow)
    omega

/-! ## Pure estimates -/

/-- `P = M²(1 + O(g))` and `M = w(1 + O(g))` give `P = w²(1 + O(g))`. -/
theorem multi_core {M : ℂ} {P w g KM KP : ℝ} (hw : 0 < w) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hKM : 0 ≤ KM) (hKP : 0 ≤ KP) (hM : ‖M - (w : ℂ)‖ ≤ KM * w * g)
    (hP : ‖(P : ℂ) - M ^ 2‖ ≤ KP * ‖M‖ ^ 2 * g) :
    |P - w ^ 2| ≤ (KP * (1 + KM) ^ 2 + KM * (2 + KM)) * w ^ 2 * g := by
  have hKMg : KM * g ≤ KM := mul_le_of_le_one_right hKM hg1
  have hwn : ‖(w : ℂ)‖ = w := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  have hMn : ‖M‖ ≤ w * (1 + KM) := by
    have := norm_le_norm_add_norm_sub' M (w : ℂ)
    rw [hwn] at this
    nlinarith
  have hMp : ‖M + w‖ ≤ w * (2 + KM) := by
    have : M + w = (M - w) + 2 * (w : ℂ) := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hwn, Complex.norm_two]
    nlinarith
  have hsq : ‖M ^ 2 - (w : ℂ) ^ 2‖ ≤ KM * w * g * (w * (2 + KM)) := by
    rw [show M ^ 2 - (w : ℂ) ^ 2 = (M - w) * (M + w) by ring, norm_mul]
    exact mul_le_mul hM hMp (norm_nonneg _) (by positivity)
  have hM2 : ‖M‖ ^ 2 ≤ (w * (1 + KM)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hMn 2
  have hPn : |P - w ^ 2| = ‖(P : ℂ) - M ^ 2 + (M ^ 2 - (w : ℂ) ^ 2)‖ := by
    rw [show (P : ℂ) - M ^ 2 + (M ^ 2 - (w : ℂ) ^ 2) = ((P - w ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hPn]
  refine (norm_add_le _ _).trans ?_
  have h1 : KP * ‖M‖ ^ 2 * g ≤ KP * (w * (1 + KM)) ^ 2 * g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM2 hKP) hg0
  nlinarith

theorem le_one_add_cube {u : ℝ} (hu : 0 ≤ u) : u ≤ 1 + u ^ 3 := by
  rcases le_total u 1 with h | h
  · nlinarith [pow_nonneg hu 3]
  · nlinarith [mul_le_mul h h zero_le_one hu]

theorem abs_sub_one_le_cube {t : ℝ} (ht : 0 ≤ t) : |t - 1| ≤ |t ^ 3 - 1| := by
  rw [show t ^ 3 - 1 = (t - 1) * (t ^ 2 + t + 1) by ring, abs_mul]
  have : 1 ≤ |t ^ 2 + t + 1| := by
    rw [abs_of_pos (by positivity)]; nlinarith
  nlinarith [abs_nonneg (t - 1)]

/-- **The shift `j_x → j(|x|)`**: with `w³g = w'³g'` (both `= b`, `w = (b/g)^{1/3}`) and
`|1/g - 1/g'| ≤ c`, `P = w²(1 + O(g))` gives `P = w'²(1 + O(g'))`. -/
theorem multi_shift {P w w' g g' K1 c : ℝ} (hw : 0 < w) (hw' : 0 < w') (hg : 0 < g) (hg' : 0 < g')
    (hg1 : g ≤ 1) (hg'1 : g' ≤ 1) (hc : 0 ≤ c) (hK1 : 0 ≤ K1)
    (hb : w ^ 3 * g = w' ^ 3 * g') (hgap : |1 / g - 1 / g'| ≤ c)
    (h : |P - w ^ 2| ≤ K1 * w ^ 2 * g) :
    |P - w' ^ 2| ≤ (K1 * (2 + c) + c * (3 + c)) * w' ^ 2 * g' := by
  set t := w / w' with htd
  set u := w' / w with hud
  have ht0 : 0 < t := div_pos hw hw'
  have hu0 : 0 < u := div_pos hw' hw
  have hwt : w = t * w' := by rw [htd, div_mul_cancel₀ _ hw'.ne']
  have hwu : w' = u * w := by rw [hud, div_mul_cancel₀ _ hw.ne']
  -- `t³ = g'/g`, `u³ = g/g'`
  have ht3 : t ^ 3 * g = g' := by
    have := hb; rw [hwt] at this
    have h3 : w' ^ 3 ≠ 0 := by positivity
    exact mul_left_cancel₀ h3 (by linear_combination this)
  have hu3 : u ^ 3 * g' = g := by
    have := hb; rw [hwu] at this
    have h3 : w ^ 3 ≠ 0 := by positivity
    exact mul_left_cancel₀ h3 (by linear_combination -this)
  have hgg : |g' - g| ≤ c * g * g' := by
    have e : g' - g = g * g' * (1 / g - 1 / g') := by field_simp
    rw [e, abs_mul, abs_of_pos (mul_pos hg hg')]
    calc g * g' * |1 / g - 1 / g'| ≤ g * g' * c := mul_le_mul_of_nonneg_left hgap (by positivity)
      _ = c * g * g' := by ring
  -- `|t³ - 1| ≤ c g'`, `u³ ≤ 1 + c`
  have ht31 : |t ^ 3 - 1| ≤ c * g' := by
    have e : t ^ 3 - 1 = (g' - g) / g := by field_simp; linarith
    rw [e, abs_div, abs_of_pos hg, div_le_iff₀ hg]; linarith
  have hu31 : u ^ 3 ≤ 1 + c := by
    have e : u ^ 3 - 1 = (g - g') / g' := by field_simp; linarith
    have : |u ^ 3 - 1| ≤ c * g := by
      rw [e, abs_div, abs_of_pos hg', div_le_iff₀ hg', abs_sub_comm]; linarith
    have hcg : c * g ≤ c := mul_le_of_le_one_right hc hg1
    linarith [le_abs_self (u ^ 3 - 1)]
  have ht3c : t ^ 3 ≤ 1 + c := by
    have hcg : c * g' ≤ c := mul_le_of_le_one_right hc hg'1
    linarith [le_abs_self (t ^ 3 - 1)]
  -- the two terms
  have hA : w ^ 2 * g = u * (w' ^ 2 * g') := by
    rw [hwu, ← hu3]; ring
  have hu2 : u ≤ 2 + c := (le_one_add_cube hu0.le).trans (by linarith)
  have hB : |w ^ 2 - w' ^ 2| ≤ c * (3 + c) * (w' ^ 2 * g') := by
    rw [hwt, show (t * w') ^ 2 - w' ^ 2 = w' ^ 2 * ((t - 1) * (t + 1)) by ring, abs_mul, abs_mul,
      abs_of_pos (by positivity : 0 < w' ^ 2), abs_of_pos (by linarith : 0 < t + 1)]
    have h1 : |t - 1| ≤ c * g' := (abs_sub_one_le_cube ht0.le).trans ht31
    have h2 : t + 1 ≤ 3 + c := by linarith [le_one_add_cube ht0.le]
    calc w' ^ 2 * (|t - 1| * (t + 1)) ≤ w' ^ 2 * (c * g' * (3 + c)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by linarith) (by positivity))
            (by positivity)
      _ = c * (3 + c) * (w' ^ 2 * g') := by ring
  have hW : 0 ≤ w' ^ 2 * g' := by positivity
  calc |P - w' ^ 2| ≤ |P - w ^ 2| + |w ^ 2 - w' ^ 2| := abs_sub_le _ _ _
    _ ≤ K1 * (u * (w' ^ 2 * g')) + c * (3 + c) * (w' ^ 2 * g') := by
        rw [← hA, ← mul_assoc]; exact add_le_add h hB
    _ ≤ K1 * ((2 + c) * (w' ^ 2 * g')) + c * (3 + c) * (w' ^ 2 * g') := by
        gcongr
    _ = (K1 * (2 + c) + c * (3 + c)) * w' ^ 2 * g' := by ring

omit [NeZero L] in
/-- `m² ≤ L^{-2(N-1)}` gives `m²(L^{k+1})² ≤ 1` for `k + 1 ≤ N - 1`. -/
theorem multi_msq_le {msq : ℝ} (hL : 1 ≤ L) (hN : 1 ≤ N) (hm0 : 0 ≤ msq)
    (hm : msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) {k : ℕ} (hk : k + 1 ≤ N - 1) :
    msq * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hp : 0 < (L : ℝ) ^ (2 * (N - 1)) := by positivity
  have e : (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) = ((L : ℝ) ^ (2 * (N - 1)))⁻¹ := by
    rw [Real.rpow_neg hL0.le, ← Real.rpow_natCast]
    congr 2
    push_cast [Nat.cast_sub hN]; ring
  rw [e] at hm
  have h1 : ((L : ℝ) ^ (k + 1)) ^ 2 ≤ (L : ℝ) ^ (2 * (N - 1)) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by exact_mod_cast hL) (by omega)
  calc msq * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ msq * (L : ℝ) ^ (2 * (N - 1)) :=
        mul_le_mul_of_nonneg_left h1 hm0
    _ ≤ ((L : ℝ) ^ (2 * (N - 1)))⁻¹ * (L : ℝ) ^ (2 * (N - 1)) :=
        mul_le_mul_of_nonneg_right hm hp.le
    _ = 1 := inv_mul_cancel₀ hp.ne'

theorem cube_rpow_third {y : ℝ} (hy : 0 < y) : (y ^ (1 / 3 : ℝ)) ^ 3 = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num

theorem sq_rpow_third {y : ℝ} (hy : 0 < y) : (y ^ (1 / 3 : ℝ)) ^ 2 = y ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num

/-! ## The objects along a trajectory and the named hypotheses -/

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `β_k = 1/ǧ_k` along the trajectory from `(b, μ₀)` at mass `m²`. -/
def betaJ (m b μ₀ : ℝ) (k : ℕ) : ℝ := 1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1

/-- `ϑ_k² = (β_k/β_ε)^{2/3}`, `β_ε = 1/b`. -/
def thetaSq (m b μ₀ : ℝ) (k : ℕ) : ℝ := (betaJ R m b μ₀ k / (1 / b)) ^ (2 / 3 : ℝ)

/-- **`M_j = 1 - b∑_{k<j} λ̂_kΓ^int_{k+1}(0,0)`** (`e:PM`), as in `MagConcl`. -/
def Mmag (m b μ₀ : ℝ) (lam : ℕ → ℂ) (j : ℕ) : ℂ :=
  1 - (b : ℂ) * ∑ k ∈ range j,
    lam k * GamInt (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

/-- **(H_λ)**: `‖λ̂_k - (ǧ_k/b)^{1/3}‖ ≤ K_λ(ǧ_k/b)^{1/3}(ǧ_k + a_k)` for `k < N_h` (the hypothesis
of `MagConcl`). -/
def HLam (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (Kl : ℝ) : Prop :=
  ∀ k < Nh, ‖lam k - ((((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
    Kl * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) *
      ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)

/-- **`thm:rginput`** (Expected result 2.2) along the trajectory from `(b, μ₀)` at mass `m²`:
for every `x ≠ 0` whose coalescence scale `j_x = Obs.coal L 0 x` is in the bulk (`j_x ≤ N_h`),
`P_{1/b}[0 ↔ x] = M_{j_x}²(1 + O(ǧ_{j_x}))`, in the form
`‖P - M_{j_x}²‖ ≤ K_P‖M_{j_x}‖²ǧ_{j_x}`. `P` is the `h = 0` connection probability at
`β = 1/b` (`Pconn`; `= b⟨ψ̄_0ψ_x⟩` at `b = μ₀ + m²`, `Pconn_eq_avg0`). -/
def RGInput (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (KP : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ‖((Pconn L N (1 / b) x : ℝ) : ℂ) - Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x) ^ 2‖ ≤
      KP * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1

end Traj

/-! ## The constants -/

/-- `c = β + 4(1+β)max(K_e, β/2) + |C_gu|` bounds `|β_{k+1} - β_k|` below the horizon. -/
def multC (L : ℕ) (cg Ke : ℝ) : ℝ :=
  betaL L + (2 * (1 + betaL L) * max Ke (betaL L / 2) * 2 + |Cgu (betaL L) cg|)

/-- The constant of `thm:multiscale`. -/
def multK (L : ℕ) (cg Ke KZ KG Kl KP : ℝ) : ℝ :=
  (KP * (1 + spinMK L cg Ke KZ Kl KG 0) ^ 2 +
      spinMK L cg Ke KZ Kl KG 0 * (2 + spinMK L cg Ke KZ Kl KG 0)) * (2 + multC L cg Ke) +
    multC L cg Ke * (3 + multC L cg Ke)

/-- **`thm:multiscale`** for given constants, along every admissible trajectory: (H_λ) and
`thm:rginput` give, for `x ≠ 0` with `j_x ≤ N_h`, `j = j(|x|) ∈ {j_x - 1, j_x}` and
`|P_{1/b}[0 ↔ x] - ϑ_j²| ≤ K ϑ_j²/β_j`. -/
def MultiConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ →
  ∀ Nh : ℕ, Nh + 2 ≤ N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (lam : ℕ → ℂ) (Kl KP : ℝ), 0 ≤ Kl → 0 ≤ KP →
    HLam R Nh m b μ₀ lam Kl → RGInput R Nh m b μ₀ lam KP →
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pconn L N (1 / b) x - thetaSq R m b μ₀ jp| ≤
        multK L cg Ke KZ KG Kl KP * thetaSq R m b μ₀ jp / betaJ R m b μ₀ jp

set_option maxHeartbeats 1000000 in
/-- **`thm:multiscale` along one trajectory** (the proof of `multiConcl_of`, per trajectory): from
the `D_ε` condition up to `N_h`, the magnetisation bound (`MagConcl` at this trajectory and `λ̂`),
the per-step band of `β_k` at this trajectory and `thm:rginput`. No final condition is used
(route (a1)). -/
theorem multiConcl_traj {L N : ℕ} [NeZero L] {κ cg cm cT ε Ke KZ KG : ℝ} (hL2 : 2 ≤ L)
    (hε1 : ε ≤ 1) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {Nh : ℕ}
    (hNh : Nh + 2 ≤ N) {m : ℝ} (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (hband : ∀ k < Nh, |1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1 -
          1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + betaL L| ≤
        2 * (1 + betaL L) * max Ke (betaL L / 2) * zA L m k +
          Cgu (betaL L) cg * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (lam : ℕ → ℂ) (Kl KP : ℝ) (hKP : 0 ≤ KP)
    (hMagT : ∀ j ≤ Nh,
      ‖(1 - (b : ℂ) * ∑ k ∈ range j,
          lam k * GamInt (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) -
        (((b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      spinMK L cg Ke KZ Kl KG 0 * (b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1)
    (hrg : RGInput R Nh m b μ₀ lam KP) (x : Lam 2 L N) (hx : x ≠ 0)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) :
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pconn L N (1 / b) x - thetaSq R m b μ₀ jp| ≤
        multK L cg Ke KZ KG Kl KP * thetaSq R m b μ₀ jp / betaJ R m b μ₀ jp := by
  obtain ⟨jp, hjpd, hjp1, hjp2⟩ := coal_jPhys (N := N) hL2 hx
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have hg : ∀ k ≤ Nh, 0 < (t k).1 := fun k hk => (hD k hk).1
  have hg1 : ∀ k ≤ Nh, (t k).1 ≤ 1 := fun k hk => ((hD k hk).2.1).trans hε1
  have hb : 0 < b := by have := hg 0 (Nat.zero_le _); rwa [htd, Hist.traj_zero] at this
  have hjpN : jp ≤ Nh := hjp1.trans hj
  set KM := spinMK L cg Ke KZ Kl KG 0 with hKMd
  set c := multC L cg Ke with hcd
  have hβ : 0 < betaL L := by
    have : 0 < Real.log L := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
    unfold betaL; have := Real.pi_pos; positivity
  have hc : 0 ≤ c := by
    have : 0 ≤ max Ke (betaL L / 2) := le_trans (by linarith) (le_max_right _ _)
    rw [hcd, multC]; positivity
  -- the magnetisation at `j_x`
  have hmag := hMagT j hj
  have hwj : 0 < (b / (t j).1) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (div_pos hb (hg j hj)) _
  have hKM : 0 ≤ KM := by
    have h0 : 0 ≤ KM * ((b / (t j).1) ^ (1 / 3 : ℝ) * (t j).1) := by
      rw [← mul_assoc]; exact (norm_nonneg _).trans hmag
    exact nonneg_of_mul_nonneg_left h0 (mul_pos hwj (hg j hj))
  have hcore := multi_core (P := Pconn L N (1 / b) x) hwj (hg j hj).le (hg1 j hj) hKM hKP hmag
    (hrg x hx hj)
  -- the gap `|β_{j_x} - β_{j(|x|)}| ≤ c`
  have hgap : |1 / (t j).1 - 1 / (t jp).1| ≤ c := by
    rcases (by omega : j = jp ∨ j = jp + 1) with e | e
    · rw [e, sub_self, abs_zero]; exact hc
    · have hk : jp < Nh := by omega
      have h1 := hband jp hk
      have hz : zA L m jp ≤ 2 := zA_le_two (by exact_mod_cast (by omega : 1 ≤ L))
        (multi_msq_le (by omega) (by omega) hm.1.le hm.2 (by omega))
      have hmx : 0 ≤ 2 * (1 + betaL L) * max Ke (betaL L / 2) := by
        have : 0 ≤ max Ke (betaL L / 2) := le_trans (by linarith) (le_max_right _ _)
        positivity
      have hz2 := mul_le_mul_of_nonneg_left hz hmx
      have hC : Cgu (betaL L) cg * (t jp).1 ≤ |Cgu (betaL L) cg| := by
        calc Cgu (betaL L) cg * (t jp).1 ≤ |Cgu (betaL L) cg| * (t jp).1 :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (hg jp hjpN).le
          _ ≤ |Cgu (betaL L) cg| * 1 :=
              mul_le_mul_of_nonneg_left (hg1 jp hjpN) (abs_nonneg _)
          _ = _ := mul_one _
      rw [e]
      have h2 := abs_le.1 h1
      rw [abs_le, hcd, multC]
      constructor <;> linarith [h2.1, h2.2]
  -- the shift
  have hwjp : 0 < (b / (t jp).1) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (div_pos hb (hg jp hjpN)) _
  have hb3 : ((b / (t j).1) ^ (1 / 3 : ℝ)) ^ 3 * (t j).1 =
      ((b / (t jp).1) ^ (1 / 3 : ℝ)) ^ 3 * (t jp).1 := by
    rw [cube_rpow_third (div_pos hb (hg j hj)), cube_rpow_third (div_pos hb (hg jp hjpN)),
      div_mul_cancel₀ _ (hg j hj).ne', div_mul_cancel₀ _ (hg jp hjpN).ne']
  have hK1 : 0 ≤ KP * (1 + KM) ^ 2 + KM * (2 + KM) := by positivity
  have hsh := multi_shift hwj hwjp (hg j hj) (hg jp hjpN) (hg1 j hj) (hg1 jp hjpN) hc hK1 hb3
    hgap hcore
  refine ⟨jp, hjpd, hjp1, hjp2, ?_⟩
  have hth : thetaSq R m b μ₀ jp = ((b / (t jp).1) ^ (1 / 3 : ℝ)) ^ 2 := by
    rw [thetaSq, betaJ, ← htd, sq_rpow_third (div_pos hb (hg jp hjpN))]
    congr 1; field_simp
  have hbe : betaJ R m b μ₀ jp = 1 / (t jp).1 := by rw [betaJ, ← htd]
  rw [hth, hbe, div_div_eq_mul_div, div_one]
  convert hsh using 1


/-- **`thm:multiscale` from `SpinConcl` and `MagConcl`** (the same constants). -/
theorem multiConcl_of {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ} (hL2 : 2 ≤ L)
    (hε1 : ε ≤ 1) (hSp : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hMag : MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG) : MultiConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ Nh hNh m hm b μ₀ hadm lam Kl KP hKl hKP hl hrg x hx hj
  obtain ⟨-, -, -, -, -, hband, -, -⟩ := hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh
  exact multiConcl_traj hL2 hε1 R hNh hm hadm.1 (hband m hm b μ₀ hadm) lam Kl KP hKP
    (hMag N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh m hm b μ₀ hadm lam Kl hKl hl) hrg x hx hj

end

end Spin2
