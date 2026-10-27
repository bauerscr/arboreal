import FRD.Lift
import FRD.Fourier
import FRD.BoundsLattice

/-!
# Lattice sums on the torus and norm comparisons (gap LS, part 1)

* `supNorm_eq_zero_iff`: `|x|_∞ = 0 ↔ x = 0`.
* `card_supNorm_le`: `#{x ∈ Λ : |x|_∞ ≤ k} ≤ (2k+1)^d`.
* `sum_supNorm_rpow_le`: for `0 < s < d` there is `C` with
  `∑_{x ≠ 0} |x|_∞^{-s} ≤ C n^{d-s}` on every torus `(ℤ/nℤ)^d`; hence (`latticeSum_le`)
  `|Λ_N|^{-1} ∑_{x ≠ 0} |x|_∞^{-s} ≤ C L^{-sN}` on `Λ_N = (ℤ/L^Nℤ)^d`.
* `eNorm z = (∑_i z_i²)^{1/2}` on `ℤ^d`, with `|z|_∞ ≤ |z| ≤ √d |z|_∞` (`supNormZ_le_eNorm`,
  `eNorm_le_supNormZ`) and `supNormZ (rep x) = supNorm x` (`supNormZ_rep_eq_supNorm`).
-/

namespace FRD

noncomputable section

open Finset Grassmann

variable {d : ℕ}

/-- The Euclidean norm `|z| = (∑_i z_i²)^{1/2}` on `ℤ^d`. -/
def eNorm (z : Zd d) : ℝ := Real.sqrt (∑ i, ((z i : ℤ) : ℝ) ^ 2)

theorem eNorm_nonneg (z : Zd d) : 0 ≤ eNorm z := Real.sqrt_nonneg _

theorem natAbs_le_eNorm (z : Zd d) (i : Fin d) : ((z i).natAbs : ℝ) ≤ eNorm z := by
  rw [eNorm]
  refine Real.le_sqrt_of_sq_le ?_
  have h : ((z i).natAbs : ℝ) ^ 2 = ((z i : ℤ) : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [h]
  exact single_le_sum (f := fun j => ((z j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)

/-- `|z|_∞ ≤ |z|`. -/
theorem supNormZ_le_eNorm (z : Zd d) : (supNormZ z : ℝ) ≤ eNorm z := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [supNormZ, eNorm_nonneg]
  · haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin d)) univ_nonempty
      fun i => (z i).natAbs
    rw [supNormZ, hi]
    exact natAbs_le_eNorm z i

/-- `|z| ≤ √d |z|_∞`. -/
theorem eNorm_le_supNormZ (z : Zd d) : eNorm z ≤ Real.sqrt d * supNormZ z := by
  rw [eNorm, ← Real.sqrt_sq (Nat.cast_nonneg (supNormZ z)), ← Real.sqrt_mul (Nat.cast_nonneg d)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ((z i : ℤ) : ℝ) ^ 2 ≤ ∑ _i : Fin d, (supNormZ z : ℝ) ^ 2 := by
        refine sum_le_sum fun i _ => ?_
        have h : ((z i : ℤ) : ℝ) ^ 2 = ((z i).natAbs : ℝ) ^ 2 := by
          rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
        rw [h]
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast natAbs_le_supNormZ z i) 2
    _ = d * (supNormZ z : ℝ) ^ 2 := by simp

theorem supNormZ_eq_zero_iff (z : Zd d) : supNormZ z = 0 ↔ z = 0 := by
  constructor
  · intro h
    funext i
    have := natAbs_le_supNormZ z i
    rw [h] at this
    simpa using Nat.le_zero.1 this
  · rintro rfl; simp [supNormZ]

variable {n : ℕ} [NeZero n]

theorem supNormZ_rep_eq_supNorm (x : Torus d n) : supNormZ (rep x) = supNorm x := by
  simp only [supNormZ, supNorm, natAbs_rep]

theorem supNorm_eq_zero_iff (x : Torus d n) : supNorm x = 0 ↔ x = 0 := by
  rw [← supNormZ_rep_eq_supNorm, supNormZ_eq_zero_iff]
  constructor
  · intro h
    rw [← prj_rep x, h]
    have := prj_sub (n := n) (0 : Zd d) 0
    simpa using this
  · rintro rfl
    funext i
    have := natAbs_rep (0 : Torus d n) i
    simp only [zabs] at this
    have h0 : ((0 : Torus d n) : Fin d → ZMod n) i = 0 := rfl
    rw [h0, ZMod.val_zero, Nat.zero_min] at this
    exact Int.natAbs_eq_zero.1 this

theorem supNorm_le_n (x : Torus d n) : supNorm x ≤ n := by
  unfold supNorm
  refine Finset.sup_le fun i _ => ?_
  unfold zabs
  exact (min_le_left _ _).trans (ZMod.val_lt _).le

/-- `#{x : |x|_∞ ≤ k} ≤ (2k+1)^d`. -/
theorem card_supNorm_le (k : ℕ) :
    (univ.filter fun x : Torus d n => supNorm x ≤ k).card ≤ (2 * k + 1) ^ d := by
  have hinj : Set.InjOn (rep : Torus d n → Zd d) (univ.filter fun x : Torus d n => supNorm x ≤ k) :=
    fun x _ y _ h => by rw [← prj_rep x, h, prj_rep]
  have hmaps : ∀ x ∈ (univ.filter fun x : Torus d n => supNorm x ≤ k),
      rep x ∈ Fintype.piFinset fun _ : Fin d => Finset.Icc (-(k : ℤ)) k := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    simp only [Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h1 := natAbs_rep x i
    have h2 : zabs ((x : Fin d → ZMod n) i) ≤ supNorm x :=
      Finset.le_sup (f := fun i => zabs ((x : Fin d → ZMod n) i)) (mem_univ i)
    omega
  refine (Finset.card_le_card_of_injOn _ hmaps hinj).trans ?_
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, prod_const, card_univ, Fintype.card_fin]
  apply le_of_eq
  congr 1
  omega

/-- The dyadic scale of `x ≠ 0`. -/
def dyad (x : Torus d n) : ℕ := Nat.log 2 (supNorm x)

theorem sum_supNorm_rpow_le_n {s : ℝ} (hs : 0 < s) (hsd : s < d) :
    ∑ x ∈ univ.filter (fun x : Torus d n => x ≠ 0), ((supNorm x : ℕ) : ℝ) ^ (-s) ≤
      (8 : ℝ) ^ d * ((2 : ℝ) ^ ((d : ℝ) - s) / ((2 : ℝ) ^ ((d : ℝ) - s) - 1)) *
        (n : ℝ) ^ ((d : ℝ) - s) := by
  set r : ℝ := (2 : ℝ) ^ ((d : ℝ) - s) with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by linarith)
  set M := Nat.log 2 n
  set S := univ.filter fun x : Torus d n => x ≠ 0
  have hk0 : ∀ x ∈ S, supNorm x ≠ 0 := by
    intro x hx
    simp only [S, mem_filter, mem_univ, true_and] at hx
    exact fun h => hx ((supNorm_eq_zero_iff x).1 h)
  -- termwise bound by the dyadic scale
  have hterm : ∀ x ∈ S, ((supNorm x : ℕ) : ℝ) ^ (-s) ≤ ((2 ^ dyad x : ℕ) : ℝ) ^ (-s) := by
    intro x hx
    have h1 : 2 ^ dyad x ≤ supNorm x := Nat.pow_log_le_self 2 (hk0 x hx)
    rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]
    refine inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _) ?_
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h1) hs.le
  have hmaps : ∀ x ∈ S, dyad x ∈ range (M + 1) := by
    intro x _
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.log_mono_right (supNorm_le_n x)
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun x => ((2 ^ dyad x : ℕ) : ℝ) ^ (-s))
  have hcount : ∀ m, (S.filter fun x => dyad x = m).card ≤ (2 * 2 ^ (m + 1) + 1) ^ d := by
    intro m
    refine (Finset.card_le_card fun x hx => ?_).trans (card_supNorm_le (2 ^ (m + 1)))
    simp only [S, mem_filter, mem_univ, true_and] at hx ⊢
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (supNorm x)
    rw [dyad] at hx
    rw [hx.2] at this
    exact this.le
  have hm : ∀ m : ℕ, ((2 * 2 ^ (m + 1) + 1) ^ d : ℕ) * (((2 ^ m : ℕ) : ℝ) ^ (-s)) ≤
      (8 : ℝ) ^ d * r ^ m := by
    intro m
    have h2m : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
    have h8 : (2 * 2 ^ (m + 1) + 1 : ℝ) ≤ 8 * 2 ^ m := by
      have := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := m)
      rw [pow_succ]; linarith
    have e1 : (((2 * 2 ^ (m + 1) + 1) ^ d : ℕ) : ℝ) ≤ (8 : ℝ) ^ d * (((2 ^ m : ℕ) : ℝ) ^ (d : ℝ)) := by
      rw [Real.rpow_natCast, ← mul_pow]
      push_cast
      exact pow_le_pow_left₀ (by positivity) h8 d
    have e2 : (((2 ^ m : ℕ) : ℝ) ^ (d : ℝ)) * (((2 ^ m : ℕ) : ℝ) ^ (-s)) = r ^ m := by
      rw [← Real.rpow_add h2m, hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      push_cast
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      ring_nf
    calc _ ≤ (8 : ℝ) ^ d * (((2 ^ m : ℕ) : ℝ) ^ (d : ℝ)) * (((2 ^ m : ℕ) : ℝ) ^ (-s)) :=
          mul_le_mul_of_nonneg_right e1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by rw [mul_assoc, e2]
  calc ∑ x ∈ S, ((supNorm x : ℕ) : ℝ) ^ (-s)
      ≤ ∑ x ∈ S, ((2 ^ dyad x : ℕ) : ℝ) ^ (-s) := sum_le_sum hterm
    _ = ∑ m ∈ range (M + 1), ∑ x ∈ S.filter (fun x => dyad x = m),
          ((2 ^ dyad x : ℕ) : ℝ) ^ (-s) := hfib.symm
    _ = ∑ m ∈ range (M + 1), ((S.filter fun x => dyad x = m).card : ℝ) *
          (((2 ^ m : ℕ) : ℝ) ^ (-s)) := by
        refine sum_congr rfl fun m _ => ?_
        rw [Finset.sum_congr rfl (fun x hx => show ((2 ^ dyad x : ℕ) : ℝ) ^ (-s) =
          ((2 ^ m : ℕ) : ℝ) ^ (-s) by rw [(mem_filter.1 hx).2]), sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ range (M + 1), (8 : ℝ) ^ d * r ^ m := by
        refine sum_le_sum fun m _ => le_trans ?_ (hm m)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount m)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (8 : ℝ) ^ d * ((r ^ (M + 1) - 1) / (r - 1)) := by rw [← mul_sum, geom_sum_eq hr1.ne']
    _ ≤ (8 : ℝ) ^ d * (r / (r - 1) * (n : ℝ) ^ ((d : ℝ) - s)) := by
        have h2M : ((2 ^ M : ℕ) : ℝ) ≤ n := by
          exact_mod_cast Nat.pow_log_le_self 2 (NeZero.ne n)
        have hX : r ^ M ≤ (n : ℝ) ^ ((d : ℝ) - s) := by
          calc r ^ M = ((2 ^ M : ℕ) : ℝ) ^ ((d : ℝ) - s) := by
                rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
                push_cast
                rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
                ring_nf
            _ ≤ _ := Real.rpow_le_rpow (Nat.cast_nonneg _) h2M (by linarith)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (r ^ (M + 1) - 1) / (r - 1) ≤ r ^ (M + 1) / (r - 1) :=
              div_le_div_of_nonneg_right (by linarith) (by linarith)
          _ = r / (r - 1) * r ^ M := by rw [pow_succ]; ring
          _ ≤ r / (r - 1) * (n : ℝ) ^ ((d : ℝ) - s) :=
              mul_le_mul_of_nonneg_left hX (div_nonneg (by linarith) (by linarith))
    _ = _ := by ring

/-- **Lattice sums**: for `0 < s < d` there is `C` with `∑_{x ≠ 0} |x|_∞^{-s} ≤ C n^{d-s}`
on every torus `(ℤ/nℤ)^d`. -/
theorem sum_supNorm_rpow_le {s : ℝ} (hs : 0 < s) (hsd : s < d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : ℕ) [NeZero n], ∑ x ∈ univ.filter (fun x : Torus d n => x ≠ 0),
      ((supNorm x : ℕ) : ℝ) ^ (-s) ≤ C * (n : ℝ) ^ ((d : ℝ) - s) := by
  have hr1 : 1 < (2 : ℝ) ^ ((d : ℝ) - s) := Real.one_lt_rpow (by norm_num) (by linarith)
  refine ⟨(8 : ℝ) ^ d * ((2 : ℝ) ^ ((d : ℝ) - s) / ((2 : ℝ) ^ ((d : ℝ) - s) - 1)), ?_,
    fun n _ => sum_supNorm_rpow_le_n hs hsd⟩
  exact mul_nonneg (by positivity) (div_nonneg (by linarith) (by linarith))

/-- **Lattice sums on `Λ_N`**: `|Λ_N|^{-1} ∑_{x ≠ 0} |x|_∞^{-s} ≤ C L^{-sN}` for `0 < s < d`. -/
theorem latticeSum_le {s : ℝ} (hs : 0 < s) (hsd : s < d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L : ℕ) [NeZero L] (N : ℕ), (Fintype.card (Torus d (L ^ N)) : ℝ)⁻¹ *
      ∑ x ∈ univ.filter (fun x : Torus d (L ^ N) => x ≠ 0), ((supNorm x : ℕ) : ℝ) ^ (-s) ≤
        C * (L : ℝ) ^ (-(s * N)) := by
  obtain ⟨C, hC0, hC⟩ := sum_supNorm_rpow_le (d := d) hs hsd
  refine ⟨C, hC0, fun L _ N => ?_⟩
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hcard : (Fintype.card (Torus d (L ^ N)) : ℝ) = ((L : ℝ) ^ N) ^ (d : ℝ) := by
    rw [card_torus, Real.rpow_natCast]
    push_cast; ring
  have hpos : (0 : ℝ) < (L : ℝ) ^ N := by positivity
  calc (Fintype.card (Torus d (L ^ N)) : ℝ)⁻¹ *
        ∑ x ∈ univ.filter (fun x : Torus d (L ^ N) => x ≠ 0), ((supNorm x : ℕ) : ℝ) ^ (-s)
      ≤ (Fintype.card (Torus d (L ^ N)) : ℝ)⁻¹ * (C * (((L ^ N : ℕ) : ℝ)) ^ ((d : ℝ) - s)) :=
        mul_le_mul_of_nonneg_left (hC (L ^ N)) (by positivity)
    _ = C * (((L : ℝ) ^ N) ^ ((d : ℝ) - s) / ((L : ℝ) ^ N) ^ (d : ℝ)) := by
        rw [hcard]; push_cast; ring
    _ = C * (L : ℝ) ^ (-(s * N)) := by
        rw [← Real.rpow_sub hpos, show (d : ℝ) - s - d = -s by ring, ← Real.rpow_natCast,
          ← Real.rpow_mul hL.le]
        ring_nf

end

end FRD
