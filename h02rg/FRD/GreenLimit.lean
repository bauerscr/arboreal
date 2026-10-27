import FRD.Kernel
import FRD.Green
import FRD.Continuity
import FRD.WN

/-!
# `e:greenfLambdaZd`

`lim_{m² ↓ 0} [(-Δ + m²)^{-1}(0, x) - t_N/|Λ_N|] = (-Δ^{ℤ^d})^{-1}(0, x) + O(L^{-(d-2)(N-1)})`,
with a constant independent of `L`, `N` and `x` (so `O(L^{-(d-2)N})` with an `L`-dependent
constant, as allowed in Sections 1–2 of `h02rg.tex`).  Here `x ∈ Λ_N` is identified with its
centred representative `r(x) ∈ ℤ^d`.
-/

namespace FRD

noncomputable section

open Finset Grassmann Filter Topology

variable (P : PtFamily) {d : ℕ}

theorem Cj_zero_x {n : ℕ} [NeZero n] (msq L : ℝ) (j : ℕ) (x : Torus d n) :
    Cj P msq L j 0 x = Cj P msq L j x 0 := fmat_symm _ _ _

theorem greenf (hd : 3 ≤ d) : ∃ K : ℝ, ∀ (L : ℕ) [NeZero L], 2 ≤ L → ∀ N : ℕ, 1 ≤ N →
    ∀ x : Torus d (L ^ N), ∃ w : ℝ,
      Tendsto (fun msq => WN P msq L N x) (𝓝[>] 0) (𝓝 w) ∧
      |w - greenZd d (rep x)| ≤ K * (L : ℝ) ^ (-(((d : ℝ) - 2) * (N - 1 : ℕ))) := by
  obtain ⟨K₀, hK₀⟩ := covZ_bound P hd
  obtain ⟨K₁, hK₁⟩ := CN_bound P hd 0 le_rfl 0
  refine ⟨|K₁| * (2 * (d : ℝ))⁻¹ + 2 * |K₀|, fun L _ hL N hN x => ?_⟩
  have hd1 : 1 ≤ d := by omega
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  set f : ℝ → ℝ := fun msq => ∑ j ∈ Finset.Ico 1 N, Cj P msq L j 0 x + CN P msq L N 0 x
  refine ⟨f 0, ?_, ?_⟩
  · -- continuity at `m² = 0`
    have hc : ContinuousOn f (Set.Ici 0) :=
      (continuousOn_finsetSum _ fun j _ => Cj_continuousOn P hd1 (by positivity) j 0 x).add
        (CN_continuousOn P hd1 (by positivity) N 0 x)
    have ht : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
      ((hc 0 Set.self_mem_Ici).tendsto).mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with msq hmsq
    exact (WN_eq P hmsq hL1.le hN x).symm
  · -- comparison with the Green's function on `ℤ^d`
    set a : ℕ → ℝ := fun j => covZ P d 0 (Set.Ioc (lowEnd L (j + 1)) ((L : ℝ) ^ (j + 1) / 2)) (rep x)
    have hs := hasSum_covZ_green P hd hL1 (rep x)
    have hsplit := hs.summable.sum_add_tsum_nat_add (N - 1)
    rw [hs.tsum_eq] at hsplit
    have hhead : ∑ j ∈ Finset.range (N - 1), a j = ∑ j ∈ Finset.Ico 1 N, Cj P 0 L j 0 x := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [add_comm 1 j, Cj_zero_x, Cj_eq_Zd P le_rfl hd1 (by positivity) (j + 1), sub_zero]
      push_cast
      exact pow_lt_pow_right₀ hL1 (by omega)
    set r : ℝ := (L : ℝ) ^ (-((d : ℝ) - 2))
    have hr0 : 0 ≤ r := by positivity
    have hr : r ≤ 1 / 2 := by
      calc r ≤ (L : ℝ) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hL1.le (by
              have : (3 : ℝ) ≤ d := by exact_mod_cast hd
              linarith)
        _ = 1 / L := by rw [Real.rpow_neg_one, one_div]
        _ ≤ 1 / 2 := by
            gcongr
            exact_mod_cast hL
    have hpow : ∀ j : ℕ, (L : ℝ) ^ (-(((d : ℝ) - 2) * j)) = r ^ j := by
      intro j; rw [neg_mul_eq_neg_mul, Real.rpow_mul_natCast (by positivity)]
    set B : ℝ := (L : ℝ) ^ (-(((d : ℝ) - 2) * (N - 1 : ℕ)))
    have hB : 0 ≤ B := by positivity
    have htail : |∑' i, a (i + (N - 1))| ≤ 2 * |K₀| * B := by
      have hb : ∀ i, ‖a (i + (N - 1))‖ ≤ |K₀| * B * r ^ i := by
        intro i
        have hz : 2 * supNormZ (rep x) < L ^ (i + (N - 1) + 2) := by
          have h1 := supNormZ_rep x
          have h2 : L ^ N < L ^ (i + (N - 1) + 2) := Nat.pow_lt_pow_right hL (by omega)
          omega
        have := hK₀ L hL (i + (N - 1)) (rep x) hz
        rw [Real.norm_eq_abs]
        refine this.trans ?_
        rw [hpow, pow_add, show B = r ^ (N - 1) from hpow _]
        calc K₀ * (r ^ i * r ^ (N - 1)) ≤ |K₀| * (r ^ i * r ^ (N - 1)) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
          _ = _ := by ring
      have hg : HasSum (fun i => |K₀| * B * r ^ i) (|K₀| * B * (1 - r)⁻¹) :=
        (hasSum_geometric_of_lt_one hr0 (by linarith)).mul_left _
      have := tsum_of_norm_bounded hg hb
      rw [Real.norm_eq_abs] at this
      refine this.trans ?_
      have h1 : (1 - r)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      calc |K₀| * B * (1 - r)⁻¹ ≤ |K₀| * B * 2 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * |K₀| * B := by ring
    have hCN : |CN P 0 L N 0 x| ≤ |K₁| * (2 * (d : ℝ))⁻¹ * B := by
      have := hK₁ L (by omega) N hN 0 le_rfl 0 0 (by simp [Grassmann.mabs])
        (by simp [Grassmann.mabs]) 0 x
      rw [nabC_zero] at this
      have h0 : Grassmann.mabs (0 : Dir d → ℕ) = 0 := by simp [Grassmann.mabs]
      simp only [h0, Nat.cast_zero, add_zero, zero_mul, zero_div, neg_zero, Real.rpow_zero,
        mul_one] at this
      refine this.trans ?_
      gcongr
      · exact le_abs_self _
    have hw : f 0 - greenZd d (rep x) = CN P 0 L N 0 x - ∑' i, a (i + (N - 1)) := by
      rw [← hsplit, hhead]; simp only [f]; ring
    rw [hw]
    calc |CN P 0 L N 0 x - ∑' i, a (i + (N - 1))|
        ≤ |CN P 0 L N 0 x| + |∑' i, a (i + (N - 1))| := abs_sub _ _
      _ ≤ |K₁| * (2 * (d : ℝ))⁻¹ * B + 2 * |K₀| * B := add_le_add hCN htail
      _ = _ := by ring

end

end FRD
