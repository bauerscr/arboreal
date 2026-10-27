import PtCorr2.Pair.PairDGeom
import Step2.Map.Geom

/-!
# Block count of the covering polymer; lattice paths

* **`nb_ballPoly_mul_le`**: `|𝓑_j(ballPoly j a R)|·L^{jd} ≤ (2(R + L^j) + 1)^d` (the ball polymer lies
  in the sup-ball of radius `R + L^j`, and every block has `L^{jd}` points);
* **`nb_ballPoly_coal_le`**: for the covering polymer of `exists_dCov_aux`
  (`R = 2^{d+1}L^j + |b - a|_∞`) and `2|a - b|_∞ < L^{j+1}` (i.e. `j ≥ j_{ab}`):
  `|𝓑_j(D)| ≤ (L + 2^{d+2} + 2)^d`, i.e. `O(L²)` in `d = 2` (`(L + 18)²`);
* **`exists_path_sum`**: every `x` of the torus is the endpoint of a nearest-neighbour path from
  `0` with at most `d|x|_∞` steps.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc Step FRD Obs2

/-! ### Lattice paths -/

theorem sum_map_flatMap {d n : ℕ} {ι : Type*} (f : ι → List (Dir d)) :
    ∀ l : List ι, (((l.flatMap f).map (dirVec (n := n))).sum : Torus d n) =
      (l.map fun i => ((f i).map (dirVec (n := n))).sum).sum
  | [] => rfl
  | i :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_map_flatMap f l]
    rfl

/-- **Nearest-neighbour paths**: `x = ∑_{e ∈ w} e` with `|w| ≤ d|x|_∞`. -/
theorem exists_path_sum {d n : ℕ} [NeZero n] (x : Torus d n) :
    ∃ w : List (Dir d), (w.map (dirVec (n := n))).sum = x ∧ w.length ≤ d * supNorm x := by
  choose r hr hr' using fun i => exists_natAbs_eq_zabs (n := n) ((x : Fin d → ZMod n) i)
  let f : Fin d → List (Dir d) := fun i =>
    List.replicate (r i).natAbs (if 0 ≤ r i then Sum.inl i else Sum.inr i)
  refine ⟨(List.finRange d).flatMap f, ?_, ?_⟩
  · rw [sum_map_flatMap, ← Fin.sum_univ_def]
    have hg : ∀ i, (((f i).map (dirVec (n := n))).sum : Torus d n) =
        (Pi.single i ((x : Fin d → ZMod n) i) : Fin d → ZMod n) := by
      intro i
      simp only [f, List.map_replicate, List.sum_replicate]
      funext k
      by_cases hk : k = i
      · subst hk
        split_ifs with h0
        · show ((r k).natAbs • (Pi.single k 1 : Fin d → ZMod n)) k = _
          rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, nsmul_eq_mul, mul_one, ← hr k]
          rw [← Int.cast_natCast, Int.natAbs_of_nonneg h0]
        · show ((r k).natAbs • (-(Pi.single k 1 : Fin d → ZMod n))) k = _
          rw [Pi.smul_apply, Pi.neg_apply, Pi.single_eq_same, Pi.single_eq_same, smul_neg,
            nsmul_eq_mul, mul_one, ← hr k]
          rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos (by omega), Int.cast_neg, neg_neg]
      · split_ifs
        · show ((r i).natAbs • (Pi.single i 1 : Fin d → ZMod n)) k = _
          rw [Pi.smul_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, smul_zero]
        · show ((r i).natAbs • (-(Pi.single i 1 : Fin d → ZMod n))) k = _
          rw [Pi.smul_apply, Pi.neg_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, neg_zero,
            smul_zero]
    rw [Finset.sum_congr rfl fun i _ => hg i]
    exact Finset.univ_sum_single (x : Fin d → ZMod n)
  · rw [List.length_flatMap]
    have e : ((List.finRange d).map fun i => (f i).length).sum = ∑ i, zabs ((x : Fin d → ZMod n) i) := by
      rw [Fin.sum_univ_def]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      simp only [f, List.length_replicate, hr' i]
    rw [e]
    calc ∑ i, zabs ((x : Fin d → ZMod n) i) ≤ ∑ _i : Fin d, supNorm x :=
          Finset.sum_le_sum fun i _ => (supNorm_le_iff x (supNorm x)).1 le_rfl i
      _ = d * supNorm x := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ### The block count of the ball polymer -/

variable {d L N : ℕ} [NeZero L]

theorem nb_ballPoly_mul_le {j : ℕ} (hj : j ≤ N) (a : Lam d L N) (R : ℕ) :
    nb j (ballPoly j a R) * L ^ (j * d) ≤ (2 * (R + L ^ j) + 1) ^ d := by
  have hpoly := (isConn_ballPoly (L := L) (N := N) j a R).1
  have hc : (ballPoly j a R).card = nb j (ballPoly j a R) * L ^ (j * d) := by
    rw [Step.card_polymer hpoly, sum_congr rfl fun b hb =>
      card_blockSet hj (mem_blockIdx_of_mem_blocks hb), sum_const, smul_eq_mul]
    rfl
  rw [← hc]
  refine (card_le_card fun y hy => ?_).trans (Step2.card_ball_le a (R + L ^ j))
  exact mem_filter.2 ⟨mem_univ _, ballPoly_local hy⟩

/-- **`|𝓑(D)| = O(L^d)`** for the covering polymer at a scale `j ≥ j_{ab}`. -/
theorem nb_ballPoly_coal_le {j : ℕ} (hj : j ≤ N) (a b : Lam d L N)
    (hab : 2 * supNorm (b - a) < L ^ (j + 1)) :
    nb j (ballPoly j a (2 ^ (d + 1) * L ^ j + supNorm (b - a))) ≤ (L + 2 ^ (d + 2) + 2) ^ d := by
  have h := nb_ballPoly_mul_le (L := L) (N := N) hj a (2 ^ (d + 1) * L ^ j + supNorm (b - a))
  have hLj : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hle : 2 * (2 ^ (d + 1) * L ^ j + supNorm (b - a) + L ^ j) + 1 ≤
      (L + 2 ^ (d + 2) + 2) * L ^ j := by
    have e1 : (L + 2 ^ (d + 2) + 2) * L ^ j = L ^ (j + 1) + 2 * (2 ^ (d + 1) * L ^ j) + 2 * L ^ j := by
      rw [pow_succ L j, show 2 ^ (d + 2) = 2 * 2 ^ (d + 1) by rw [pow_succ 2 (d + 1)]; ring]; ring
    rw [e1]; omega
  have h2 : nb j (ballPoly j a (2 ^ (d + 1) * L ^ j + supNorm (b - a))) * L ^ (j * d) ≤
      (L + 2 ^ (d + 2) + 2) ^ d * L ^ (j * d) :=
    h.trans ((Nat.pow_le_pow_left hle d).trans_eq (by rw [mul_pow, ← pow_mul, mul_comm j d]))
  exact Nat.le_of_mul_le_mul_right h2 (pow_pos hLj d |>.trans_eq (by rw [← pow_mul]))

end

end PtCorr2
