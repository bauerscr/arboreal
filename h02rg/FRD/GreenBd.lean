import FRD.Kernel
import FRD.Green
import FRD.Pt
import FRD.PtAverage
import FRD.PtPre
import FRD.LatticeSum

-- Merged from `FRD/PtConstruction.lean` (phase 3).
section

/-!
# Construction of a family `P_t` (`e:decomp-Pt`)

Outline (see `FRD.PtFourier`, `FRD.PtCot`, `FRD.PtPre`, `FRD.PtAverage`):

* `g₀` is a smooth even bump supported in `[-1/2, 1/2]`, `f = g₀ ⋆ g₀` is supported in `[-1, 1]`
  and `ψ = 𝓕 f = (𝓕 g₀)² ≥ 0` is a Schwartz function.
* `Q_t(u) = ∑_{|n| ≤ ⌊t⌋} f(-n/t) T_n(1 - u)`; by Poisson summation, with `u = 1 - cos 2πx`,
  `Q_t(u) = ∑_k t ψ(t(x + k)) ≥ 0`, and `∫_0^∞ Q_t(u) dt = c₀ ∑_k (x+k)^{-2} = 2π² c₀ / u`
  (using `∑_k (x+k)^{-2} = π²/sin²(πx)`, derived from the cotangent series).
* `P⁰_t = 0` for `t < 1`, `P⁰_t = Q_t / (2π² c₀ t) + A 1_{t ≤ 2}` for `t ≥ 1`.
* `P_t = ∑_j w_j 4^{-j} P⁰_{t/2^j}` (with `w_j ∝ 1/j!`) is an average over dyadic scales, which
  gives the positivity of the tails since `P⁰ ≥ A > 0` on `[1, 2]`.
-/

namespace FRD

/-- There is a family of polynomials with the properties `e:decomp-Pt`. -/
theorem exists_PtFamily : Nonempty PtFamily := ⟨PtF.prePt.toPtFamily⟩

/-- A fixed choice of the family `P_t`. -/
noncomputable def stdPt : PtFamily := Classical.choice exists_PtFamily

end FRD

end

/-!
# Bounds on the Green's function of `ℤ^d` (gap LS, part 2)

* `greenZd_zero_pos`: `0 < (-Δ^{ℤ^d})^{-1}(0,0)` for `d ≥ 3`.
* `covZ_eq_zero_of_le`: the `ℤ^d` kernels `c_{j+1}` have range `L^{j+1}/2`.
* `greenZd_bound`: `|G(z)| ≤ C (|z|_∞ + 1)^{-(d-2)}` for all `z ∈ ℤ^d`, and hence
  (`greenZd_bound_supNorm`, `greenZd_bound_eNorm`) `|G(z)| ≤ C |z|_∞^{-(d-2)}` and
  `|G(z)| ≤ C |z|^{-(d-2)}` for `z ≠ 0`.
-/

namespace FRD

noncomputable section

open Finset MeasureTheory Set Grassmann

variable {d : ℕ}

/-- Finite range of the `ℤ^d` kernels: `c_{j+1}(z) = 0` if `|z|_∞ ≥ L^{j+1}/2`. -/
theorem covZ_eq_zero_of_le (hd : 1 ≤ d) {L : ℕ} (hL : 1 ≤ L) (j : ℕ) (z : Zd d)
    (h : (L : ℝ) ^ (j + 1) / 2 ≤ supNormZ z) :
    covZ stdPt d 0 (Ioc (lowEnd L (j + 1)) ((L : ℝ) ^ (j + 1) / 2)) z = 0 := by
  set n := 2 * supNormZ z + L ^ (j + 1) + 1
  haveI : NeZero n := ⟨by omega⟩
  have hn : (L : ℝ) ^ (j + 1) < n := by
    have : ((L ^ (j + 1) : ℕ) : ℝ) < n := by exact_mod_cast (by omega : L ^ (j + 1) < n)
    exact_mod_cast this
  have hz : 2 * supNormZ z < n := by omega
  have hz' : z = rep (prj z : Torus d n) := eq_rep rfl hz
  have heq := Cj_eq_Zd stdPt le_rfl hd (L := L) (Nat.cast_nonneg _) (j + 1) hn
    (prj z : Torus d n) 0
  rw [sub_zero, ← hz'] at heq
  rw [← heq]
  apply Cj_finiteRange stdPt le_rfl (by exact_mod_cast hL) (j + 1)
  rw [sub_zero, ← supNormZ_rep_eq_supNorm, ← hz']
  exact h

/-- **Green's function bound**: `|G(z)| ≤ C (|z|_∞ + 1)^{-(d-2)}` on `ℤ^d`, `d ≥ 3`. -/
theorem greenZd_bound (hd : 3 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Zd d,
    |greenZd d z| ≤ C * ((supNormZ z : ℝ) + 1) ^ (-((d : ℝ) - 2)) := by
  obtain ⟨K, hK⟩ := covZ_bound stdPt hd
  set K' := max K 0 with hK'
  set α : ℝ := (d : ℝ) - 2 with hα
  have hα1 : 1 ≤ α := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set ρ : ℝ := (2 : ℝ) ^ (-α) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow : ∀ m : ℕ, (2 : ℝ) ^ (-(α * m)) = ρ ^ m := by
    intro m
    rw [hρ, ← neg_mul, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  refine ⟨K' / (1 - ρ), div_nonneg (le_max_right _ _) (by linarith), fun z => ?_⟩
  set r := supNormZ z
  set j₀ := Nat.clog 2 (r + 1)
  have hj₀ : r + 1 ≤ 2 ^ j₀ := Nat.le_pow_clog (by norm_num) _
  set a : ℕ → ℝ := fun j => covZ stdPt d 0 (Ioc (lowEnd 2 (j + 1)) ((2 : ℝ) ^ (j + 1) / 2)) z
  have hs : HasSum a (greenZd d z) := hasSum_covZ_green stdPt hd (by norm_num) z
  have hzero : ∀ j < j₀, a j = 0 := by
    intro j hj
    have h1 : 2 ^ j < r + 1 := Nat.pow_lt_of_lt_clog hj
    have h2 : (2 : ℝ) ^ (j + 1) / 2 ≤ r := by
      rw [pow_succ, mul_div_cancel_right₀ _ two_ne_zero]
      exact_mod_cast (by omega : 2 ^ j ≤ r)
    have := covZ_eq_zero_of_le (by omega) (L := 2) (by norm_num) j z (by exact_mod_cast h2)
    simpa [a] using this
  have hshift : HasSum (fun i => a (i + j₀)) (greenZd d z) := by
    have := (hasSum_nat_add_iff' j₀).2 hs
    rwa [Finset.sum_eq_zero (fun i hi => hzero i (mem_range.1 hi)), sub_zero] at this
  have hbd : ∀ i, |a (i + j₀)| ≤ K' * ρ ^ j₀ * ρ ^ i := by
    intro i
    have h2 : 2 * supNormZ z < 2 ^ (i + j₀ + 2) := by
      have : 2 ^ j₀ ≤ 2 ^ (i + j₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ (i + j₀ + 2) = 4 * 2 ^ (i + j₀) := by ring
      omega
    have hb := hK 2 le_rfl (i + j₀) z h2
    simp only [Nat.cast_ofNat] at hb
    calc |a (i + j₀)| ≤ K * (2 : ℝ) ^ (-(α * ((i + j₀ : ℕ) : ℝ))) := hb
      _ ≤ K' * (2 : ℝ) ^ (-(α * ((i + j₀ : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by norm_num) _)
      _ = K' * ρ ^ j₀ * ρ ^ i := by rw [hpow, pow_add]; ring
  have hg : HasSum (fun i : ℕ => K' * ρ ^ j₀ * ρ ^ i) (K' * ρ ^ j₀ * (1 - ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0.le hρ1).mul_left _
  have habs : |greenZd d z| ≤ K' * ρ ^ j₀ * (1 - ρ)⁻¹ := by
    rw [abs_le]
    constructor
    · have := hasSum_le (fun i => neg_le_of_abs_le (hbd i)) hg.neg hshift
      linarith
    · exact hasSum_le (fun i => le_of_abs_le (hbd i)) hshift hg
  have hρj : ρ ^ j₀ ≤ ((r : ℝ) + 1) ^ (-α) := by
    have e : ρ ^ j₀ = ((2 : ℝ) ^ j₀) ^ (-α) := by
      rw [hρ, ← Real.rpow_natCast ((2 : ℝ) ^ (-α)) j₀, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast (2 : ℝ) j₀, ← Real.rpow_mul (by norm_num), mul_comm]
    rw [e, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 ^ j₀),
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ (r : ℝ) + 1)]
    refine inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) ?_
    refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
    exact_mod_cast hj₀
  calc |greenZd d z| ≤ K' * ρ ^ j₀ * (1 - ρ)⁻¹ := habs
    _ ≤ K' * ((r : ℝ) + 1) ^ (-α) * (1 - ρ)⁻¹ := by
        have h1 : 0 ≤ K' := le_max_right _ _
        have h2 : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.2 (by linarith)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρj h1) h2
    _ = K' / (1 - ρ) * ((r : ℝ) + 1) ^ (-α) := by ring

theorem one_le_supNormZ {z : Zd d} (hz : z ≠ 0) : 1 ≤ supNormZ z := by
  rcases Nat.eq_zero_or_pos (supNormZ z) with h | h
  · exact absurd ((supNormZ_eq_zero_iff z).1 h) hz
  · exact h

/-- `|G(z)| ≤ C |z|_∞^{-(d-2)}` for `z ≠ 0`. -/
theorem greenZd_bound_supNorm (hd : 3 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Zd d, z ≠ 0 →
    |greenZd d z| ≤ C * (supNormZ z : ℝ) ^ (-((d : ℝ) - 2)) := by
  obtain ⟨C, hC0, hC⟩ := greenZd_bound hd
  refine ⟨C, hC0, fun z hz => (hC z).trans ?_⟩
  have h1 : (1 : ℝ) ≤ supNormZ z := by exact_mod_cast one_le_supNormZ hz
  have hα : 0 ≤ (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine mul_le_mul_of_nonneg_left ?_ hC0
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_le_rpow (by linarith) (by linarith) hα)

/-- `|G(z)| ≤ C |z|^{-(d-2)}` for `z ≠ 0` (Euclidean norm). -/
theorem greenZd_bound_eNorm (hd : 3 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Zd d, z ≠ 0 →
    |greenZd d z| ≤ C * eNorm z ^ (-((d : ℝ) - 2)) := by
  obtain ⟨C, hC0, hC⟩ := greenZd_bound_supNorm hd
  have hα : 0 ≤ (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < d))
  refine ⟨C * Real.sqrt d ^ ((d : ℝ) - 2), by positivity, fun z hz => (hC z hz).trans ?_⟩
  have h1 : (1 : ℝ) ≤ supNormZ z := by exact_mod_cast one_le_supNormZ hz
  have he : (1 : ℝ) ≤ eNorm z := h1.trans (supNormZ_le_eNorm z)
  have hle : eNorm z / Real.sqrt d ≤ supNormZ z := by
    rw [div_le_iff₀ hsd, mul_comm]; exact eNorm_le_supNormZ z
  have hpos : 0 < eNorm z / Real.sqrt d := div_pos (by linarith) hsd
  calc C * (supNormZ z : ℝ) ^ (-((d : ℝ) - 2))
      ≤ C * (eNorm z / Real.sqrt d) ^ (-((d : ℝ) - 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        rw [Real.rpow_neg (by positivity), Real.rpow_neg hpos.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hpos _) (Real.rpow_le_rpow hpos.le hle hα)
    _ = C * Real.sqrt d ^ ((d : ℝ) - 2) * eNorm z ^ (-((d : ℝ) - 2)) := by
        rw [Real.div_rpow (by linarith) hsd.le, Real.rpow_neg hsd.le, div_inv_eq_mul]
        ring

end

end FRD
