import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Heat kernel on the unit circle / torus (B1, continuum torus objects)

We use Mathlib's `cosKernel a s = ∑ₙ cos (2π a n) e^{-π n² s}` (a function on `UnitAddCircle`),
which in heat-kernel normalisation is `p_t(a) = cosKernel a (4π t)`, the kernel of `e^{tΔ}`.
Its image (Poisson) form `cosKernel a s = s^{-1/2} ∑ₙ e^{-π (n+a)²/s}` comes from
`evenKernel_functional_equation`.
-/

open Real Set Filter Topology MeasureTheory HurwitzZeta

noncomputable section

namespace Cont

/-- `cosKernel y s` as a real series indexed by `ℕ` (constant term split off). -/
lemma b1_hasSum_cosK (y : ℝ) {s : ℝ} (hs : 0 < s) :
    HasSum (fun n : ℕ ↦ 2 * Real.cos (2 * π * y * (n + 1)) * rexp (-π * (n + 1) ^ 2 * s))
      (cosKernel y s - 1) :=
  hasSum_nat_cosKernel₀ y hs

lemma b1_hasSum_cosK0 {s : ℝ} (hs : 0 < s) :
    HasSum (fun n : ℕ ↦ 2 * rexp (-π * (n + 1) ^ 2 * s)) (cosKernel 0 s - 1) := by
  have := hasSum_nat_cosKernel₀ 0 hs
  simpa using this

lemma b1_cosK0_sub_one_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ cosKernel 0 s - 1 :=
  (b1_hasSum_cosK0 hs).nonneg fun _ ↦ by positivity

/-- `|cosKernel y s - 1| ≤ cosKernel 0 s - 1`. -/
lemma b1_abs_cosK_sub_one_le (y : ℝ) {s : ℝ} (hs : 0 < s) :
    |cosKernel y s - 1| ≤ cosKernel 0 s - 1 := by
  have h := (b1_hasSum_cosK y hs).norm_le_of_bounded (b1_hasSum_cosK0 hs) fun n ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_two]
    have := abs_cos_le_one (2 * π * y * (n + 1))
    have := exp_pos (-π * (n + 1) ^ 2 * s)
    nlinarith
  simpa [Real.norm_eq_abs] using h

/-- Exponential decay of `cosKernel 0 s - 1` for `s ≥ 1`. -/
lemma b1_cosK0_decay {s : ℝ} (hs : 1 ≤ s) :
    cosKernel 0 s - 1 ≤ (cosKernel 0 1 - 1) * rexp (-π * (s - 1)) := by
  have h1 := b1_hasSum_cosK0 (lt_of_lt_of_le one_pos hs)
  have h2 := (b1_hasSum_cosK0 one_pos).mul_right (rexp (-π * (s - 1)))
  refine hasSum_le (fun n ↦ ?_) h1 h2
  rw [mul_assoc 2 (rexp _), ← exp_add]
  gcongr
  have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have : (1 : ℝ) * (s - 1) ≤ ((n : ℝ) + 1) ^ 2 * (s - 1) := by gcongr
  nlinarith [pi_pos]

/-- Continuity of `y ↦ cosKernel y s` for fixed `s > 0`. -/
lemma b1_continuous_cosK {s : ℝ} (hs : 0 < s) : Continuous fun y : ℝ ↦ cosKernel y s := by
  have heq : (fun y : ℝ ↦ cosKernel y s) = fun y ↦ 1 + ∑' n : ℕ,
      2 * Real.cos (2 * π * y * (n + 1)) * rexp (-π * (n + 1) ^ 2 * s) := by
    funext y; rw [(b1_hasSum_cosK y hs).tsum_eq]; ring
  rw [heq]
  refine continuous_const.add (continuous_tsum (fun n ↦ by fun_prop)
    (b1_hasSum_cosK0 hs).summable fun n y ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_two]
  have := abs_cos_le_one (2 * π * y * (n + 1))
  have := exp_pos (-π * (n + 1) ^ 2 * s)
  nlinarith

/-- The image constant `K = ∑ₙ e^{-π n²/32}`. -/
def b1K : ℝ := evenKernel 0 (1 / 32)

lemma b1_hasSum_K : HasSum (fun n : ℤ ↦ rexp (-π * (n : ℝ) ^ 2 * (1 / 32))) b1K := by
  have := hasSum_int_evenKernel 0 (t := 1 / 32) (by norm_num)
  simpa [b1K] using this

lemma b1K_nonneg : 0 ≤ b1K := b1_hasSum_K.nonneg fun _ ↦ (exp_pos _).le

lemma b1_sq_ge_of_abs_le {y : ℝ} (hy : |y| ≤ 3 / 4) {n : ℤ} (hn : n ≠ 0) :
    (n : ℝ) ^ 2 / 16 ≤ ((n : ℝ) + y) ^ 2 ∧ 1 ≤ (n : ℝ) ^ 2 := by
  rw [abs_le] at hy
  rcases lt_or_gt_of_ne hn with h | h
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr h
    constructor <;> nlinarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    constructor <;> nlinarith

/-- Image decomposition of `evenKernel`: `evenKernel y u = e^{-π y² u} + R`,
`0 ≤ R ≤ K e^{-π u/32}` for `|y| ≤ 3/4`, `u ≥ 1`. -/
lemma b1_evenK_decomp {y : ℝ} (hy : |y| ≤ 3 / 4) {u : ℝ} (hu : 1 ≤ u) :
    0 ≤ evenKernel y u - rexp (-π * y ^ 2 * u) ∧
      evenKernel y u - rexp (-π * y ^ 2 * u) ≤ b1K * rexp (-π * u / 32) := by
  have h0 := hasSum_ite_sub_hasSum (hasSum_int_evenKernel y (lt_of_lt_of_le one_pos hu)) 0
  simp only [Int.cast_zero, zero_add] at h0
  constructor
  · exact h0.nonneg fun n ↦ by split_ifs <;> positivity
  · refine hasSum_le (fun n ↦ ?_) h0 (b1_hasSum_K.mul_right (rexp (-π * u / 32)))
    split_ifs with hn
    · positivity
    · obtain ⟨h1, h2⟩ := b1_sq_ge_of_abs_le hy hn
      rw [← exp_add]
      gcongr
      have h3 : (n : ℝ) ^ 2 * 1 ≤ (n : ℝ) ^ 2 * u := by gcongr
      have h4 : 1 * u ≤ (n : ℝ) ^ 2 * u := by gcongr
      have h5 : (n : ℝ) ^ 2 / 16 * u ≤ ((n : ℝ) + y) ^ 2 * u := by gcongr
      have h6 : ((n : ℝ) ^ 2 + u) / 32 ≤ ((n : ℝ) + y) ^ 2 * u := by linarith
      have := mul_le_mul_of_nonneg_left h6 pi_pos.le
      nlinarith [pi_pos]

/-- Poisson form: `cosKernel y s = evenKernel y (1/s) / √s`. -/
lemma b1_cosK_eq_evenK (y : ℝ) {s : ℝ} (hs : 0 < s) :
    cosKernel y s = evenKernel y (1 / s) / Real.sqrt s := by
  have h := evenKernel_functional_equation (y : UnitAddCircle) (1 / s)
  rw [one_div_one_div, ← Real.sqrt_eq_rpow, Real.sqrt_div' _ hs.le, Real.sqrt_one] at h
  rw [h]
  have : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  field_simp

lemma b1_exp_div_le {c s : ℝ} (hc : 0 < c) (hs : 0 < s) : rexp (-c / s) / s ≤ 1 / c := by
  have hu : 0 < c / s := div_pos hc hs
  have h1 := add_one_le_exp (c / s)
  have h2 : rexp (-c / s) * rexp (c / s) = 1 := by rw [← exp_add]; ring_nf; simp
  rw [div_le_div_iff₀ hs hc]
  have : c / s * s = c := by field_simp
  nlinarith [exp_pos (-c / s), exp_pos (c / s)]

/-- The torus heat kernel (in Mathlib normalisation `s = 4π t`):
`Θ_s(x) = ∏ᵢ cosKernel (x i) s`, `x ∈ 𝕋² = UnitAddTorus (Fin 2)`. -/
def torusHeat (s : ℝ) (x : UnitAddTorus (Fin 2)) : ℝ := ∏ i, cosKernel (x i) s

lemma torusHeat_two (s : ℝ) (x : UnitAddTorus (Fin 2)) :
    torusHeat s x = cosKernel (x 0) s * cosKernel (x 1) s := by
  simp [torusHeat, Fin.prod_univ_two]

/-- The constant of the large-time bound. -/
def b1C : ℝ := (cosKernel 0 1 - 1) * (2 + (cosKernel 0 1 - 1)) * rexp π

/-- Large-time bound `|Θ_s(x) - 1| ≤ C e^{-π s}` for `s ≥ 1`. -/
lemma b1_torusHeat_large (x : UnitAddTorus (Fin 2)) {s : ℝ} (hs : 1 ≤ s) :
    |torusHeat s x - 1| ≤ b1C * rexp (-π * s) := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  rw [torusHeat_two]
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (x 0)
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk_surjective (x 1)
  rw [← ha, ← hb]
  set E := cosKernel 0 s - 1
  set E1 := cosKernel 0 1 - 1
  have hE : 0 ≤ E := b1_cosK0_sub_one_nonneg hs0
  have hE1 : 0 ≤ E1 := b1_cosK0_sub_one_nonneg one_pos
  have hdec : E ≤ E1 * rexp (-π * (s - 1)) := b1_cosK0_decay hs
  have hw : rexp (-π * (s - 1)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [pi_pos])
  have hA := b1_abs_cosK_sub_one_le a hs0
  have hB := b1_abs_cosK_sub_one_le b hs0
  set A := cosKernel (a : UnitAddCircle) s
  set B := cosKernel (b : UnitAddCircle) s
  have hBabs : |B| ≤ 1 + E1 := by
    have : |B| ≤ |B - 1| + 1 := by
      have := abs_sub_abs_le_abs_sub B 1; simp at this; linarith
    nlinarith
  have key : |A * B - 1| ≤ |A - 1| * |B| + |B - 1| := by
    have : A * B - 1 = (A - 1) * B + (B - 1) := by ring
    rw [this, ← abs_mul]; exact abs_add_le _ _
  have hexp : rexp (-π * (s - 1)) = rexp π * rexp (-π * s) := by rw [← exp_add]; ring_nf
  calc |A * B - 1| ≤ |A - 1| * |B| + |B - 1| := key
    _ ≤ E * (1 + E1) + E := by gcongr
    _ ≤ E1 * rexp (-π * (s - 1)) * (1 + E1) + E1 * rexp (-π * (s - 1)) := by gcongr
    _ = b1C * rexp (-π * s) := by rw [hexp]; unfold b1C; ring

/-- The constant of the small-time remainder bound. -/
def b1M : ℝ := (2 * b1K + b1K ^ 2) * (32 / π)

/-- Small-time decomposition: for `|y i| ≤ 3/4` and `0 < s ≤ 1`,
`0 ≤ Θ_s(π y) - s⁻¹ e^{-π |y|²/s} ≤ M`. -/
lemma b1_torusHeat_small {y₀ y₁ : ℝ} (h₀ : |y₀| ≤ 3 / 4) (h₁ : |y₁| ≤ 3 / 4) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) :
    0 ≤ cosKernel y₀ s * cosKernel y₁ s - rexp (-π * (y₀ ^ 2 + y₁ ^ 2) / s) / s ∧
      cosKernel y₀ s * cosKernel y₁ s - rexp (-π * (y₀ ^ 2 + y₁ ^ 2) / s) / s ≤ b1M := by
  have hu : 1 ≤ 1 / s := by rw [le_div_iff₀ hs]; linarith
  obtain ⟨a0, a1⟩ := b1_evenK_decomp h₀ hu
  obtain ⟨c0, c1⟩ := b1_evenK_decomp h₁ hu
  rw [b1_cosK_eq_evenK _ hs, b1_cosK_eq_evenK _ hs]
  set e0 := rexp (-π * y₀ ^ 2 * (1 / s))
  set e1 := rexp (-π * y₁ ^ 2 * (1 / s))
  set R0 := evenKernel (y₀ : UnitAddCircle) (1 / s) - e0
  set R1 := evenKernel (y₁ : UnitAddCircle) (1 / s) - e1
  set w := rexp (-π * (1 / s) / 32)
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hsq0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have he : rexp (-π * (y₀ ^ 2 + y₁ ^ 2) / s) = e0 * e1 := by
    rw [← exp_add]; congr 1; field_simp; ring
  have hprod : evenKernel (y₀ : UnitAddCircle) (1 / s) / Real.sqrt s *
      (evenKernel (y₁ : UnitAddCircle) (1 / s) / Real.sqrt s) - e0 * e1 / s =
      (e0 * R1 + R0 * e1 + R0 * R1) / s := by
    rw [div_mul_div_comm, hsq]; simp only [R0, R1]; field_simp; ring
  rw [he, hprod]
  have he0 : e0 ≤ 1 := exp_le_one_iff.mpr (by
    have : 0 ≤ y₀ ^ 2 * (1 / s) := by positivity
    nlinarith [pi_pos])
  have he1 : e1 ≤ 1 := exp_le_one_iff.mpr (by
    have : 0 ≤ y₁ ^ 2 * (1 / s) := by positivity
    nlinarith [pi_pos])
  have hw1 : w ≤ 1 := exp_le_one_iff.mpr (by
    have : 0 ≤ π * (1 / s) := by positivity
    linarith)
  have hK := b1K_nonneg
  have hw0 : 0 < w := exp_pos _
  have he0' : 0 < e0 := exp_pos _
  have he1' : 0 < e1 := exp_pos _
  constructor
  · positivity
  · have hws : w / s ≤ 32 / π := by
      have := b1_exp_div_le (c := π / 32) (by positivity) hs
      have hw' : w = rexp (-(π / 32) / s) := by simp only [w]; congr 1; field_simp
      rw [hw']; simpa using this
    have hnum : e0 * R1 + R0 * e1 + R0 * R1 ≤ (2 * b1K + b1K ^ 2) * w := by
      have : R0 * R1 ≤ (b1K * w) * (b1K * w) := mul_le_mul a1 c1 c0 (by positivity)
      have : b1K * w * (b1K * w) ≤ b1K ^ 2 * w := by nlinarith [mul_nonneg hK hK]
      have : e0 * R1 ≤ 1 * (b1K * w) := mul_le_mul he0 c1 c0 zero_le_one
      have : R0 * e1 ≤ (b1K * w) * 1 := mul_le_mul a1 he1 he1'.le (by positivity)
      nlinarith
    calc (e0 * R1 + R0 * e1 + R0 * R1) / s ≤ (2 * b1K + b1K ^ 2) * w / s := by gcongr
      _ = (2 * b1K + b1K ^ 2) * (w / s) := by ring
      _ ≤ b1M := by unfold b1M; gcongr

end Cont
