import Spin2.Multiscale.ConnSym
import Obs.Norm

/-!
# B3, T1: the shift lemma and the block geometry of the shift–relocate–restart route

Note `b3_note` (Log.md, "B3"): to compare `P(x)` and `P(y)` with `w = y - x` small, write both
as connection probabilities with the **same far point** `t + x`:

* **`cs_shift`**: `P(x) = P[t ↔ t + x]`, `P(y) = P[t - w ↔ t + x]` (exact, `PconnXY_eq`), for every `t`.
* `csCentre m`: the point with all coordinates `⌊L^m/2⌋`. It is the centre of the scale-`m` block `0`.
* **`cs_blk_ball`**: if `m ≤ N`, every `z` with `4|z - t|_∞ ≤ L^m` lies in the block `0` at every
  scale `k ≥ m`. Hence (**`cs_blk_pair`**) `t` and `t - w` lie in the same block at all scales
  `k ≥ m` when `4|w|_∞ ≤ L^m`. The distance to the block boundary is controlled by
  **`cs_blk_ball'`**: the ball of radius `L^m/4 - |w|_∞` around `t - w` stays in the block.
* `cs_four_le`: `|w|_∞ ≤ L^{m-r}` and `4 ≤ L^r` (`r ≤ m`) give `4|w|_∞ ≤ L^m`.
* **`cs_coal_eq`**: the coalescence scales are `j_c(t, t + x) = j_c(0, x)` and
  `j_c(t - w, t + x) = j_c(0, y)`.
* **`cs_coal_ge`**, **`cs_coal_gt`**: if `L^N ≤ L^c |x|_∞` (physical distance `|x| ≥ L^{-c}`), then
  `N - c ≤ j_c(0, x)`, and `m < j_c` when `m + c < N`.
-/

namespace Spin2

noncomputable section

set_option linter.unusedSectionVars false

open Finset Grassmann Loc

variable {d L N : ℕ} [NeZero L]

/-! ### The shift -/

/-- **The shift** (`b3_note`, step 1): `P(x) = P[t ↔ t + x]` and `P(y) = P[t - (y - x) ↔ t + x]`. -/
theorem cs_shift (β : ℝ) (t x y : Lam 2 L N) :
    Pconn L N β x = PconnXY L N β t (t + x) ∧
      Pconn L N β y = PconnXY L N β (t - (y - x)) (t + x) := by
  refine ⟨?_, ?_⟩
  · rw [PconnXY_eq]; congr 1; abel
  · rw [PconnXY_eq]; congr 1; abel

/-! ### The centre of a block -/

variable (d L N) in
/-- The centre `(⌊L^m/2⌋, …)` of the scale-`m` block `0`. -/
def csCentre (m : ℕ) : Lam d L N := fun _ => (((L ^ m / 2 : ℕ) : ℤ) : ZMod (L ^ N))

theorem cs_zabs_le_supNorm (u : Lam d L N) (i : Fin d) :
    zabs ((u : Fin d → ZMod (L ^ N)) i) ≤ supNorm u :=
  Finset.le_sup (f := fun i => zabs ((u : Fin d → ZMod (L ^ N)) i)) (mem_univ i)

/-- Points within `L^m/4` of the centre have all coordinates `< L^m`. -/
theorem cs_val_lt {m : ℕ} (hm : m ≤ N) {z : Lam d L N}
    (hz : 4 * supNorm (z - csCentre d L N m) ≤ L ^ m) (i : Fin d) :
    ((z : Fin d → ZMod (L ^ N)) i).val < L ^ m := by
  set u := z - csCentre d L N m with hu
  obtain ⟨r, hr, hra⟩ := FRD.exists_natAbs_eq_zabs ((u : Fin d → ZMod (L ^ N)) i)
  have hle := cs_zabs_le_supNorm u i
  have hP : L ^ m ≤ L ^ N := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) hm
  have hzi : (z : Fin d → ZMod (L ^ N)) i = (((L ^ m / 2 : ℕ) : ℤ) + r : ℤ) := by
    have : z = csCentre d L N m + u := by rw [hu]; abel
    rw [this]
    show ((((L ^ m / 2 : ℕ) : ℤ) : ZMod (L ^ N))) + (u : Fin d → ZMod (L ^ N)) i = _
    rw [← hr]; push_cast; rfl
  rw [hzi]
  have hpos : 0 < L ^ m := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) m
  have hr1 : r.natAbs * 4 ≤ L ^ m := by omega
  have h0 : 0 ≤ ((L ^ m / 2 : ℕ) : ℤ) + r := by omega
  have h1 : ((L ^ m / 2 : ℕ) : ℤ) + r < (L ^ m : ℕ) := by omega
  have h1' : ((L ^ m / 2 : ℕ) : ℤ) + r < ((L ^ N : ℕ) : ℤ) := by
    have : ((L ^ m : ℕ) : ℤ) ≤ ((L ^ N : ℕ) : ℤ) := by exact_mod_cast hP
    omega
  have hv := ZMod.val_intCast (n := L ^ N) (((L ^ m / 2 : ℕ) : ℤ) + r)
  rw [Int.emod_eq_of_lt h0 (by exact_mod_cast h1')] at hv
  have : ((((((L ^ m / 2 : ℕ) : ℤ) + r : ℤ) : ZMod (L ^ N)).val : ℕ) : ℤ) < ((L ^ m : ℕ) : ℤ) := by
    rw [hv]; exact h1
  exact_mod_cast this

/-- A point all of whose coordinates are `< L^m` is in the block `0` at every scale `k ≥ m`. -/
theorem cs_blk_zero {m k : ℕ} (hmk : m ≤ k) {z : Lam d L N}
    (hz : ∀ i, ((z : Fin d → ZMod (L ^ N)) i).val < L ^ m) : blk k z = 0 := by
  funext i
  show ((z : Fin d → ZMod (L ^ N)) i).val / L ^ k = 0
  exact Nat.div_eq_of_lt (lt_of_lt_of_le (hz i)
    (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) hmk))

/-- **The ball of radius `L^m/4` around the centre** lies in the block `0` at every scale `≥ m`. -/
theorem cs_blk_ball {m : ℕ} (hm : m ≤ N) {z : Lam d L N}
    (hz : 4 * supNorm (z - csCentre d L N m) ≤ L ^ m) {k : ℕ} (hmk : m ≤ k) :
    blk k z = 0 :=
  cs_blk_zero hmk (cs_val_lt hm hz)

theorem cs_blk_centre {m : ℕ} (hm : m ≤ N) {k : ℕ} (hmk : m ≤ k) :
    blk k (csCentre d L N m) = 0 :=
  cs_blk_ball hm (by rw [sub_self, supNorm_zero]; omega) hmk

/-- **Block geometry of the shift**: `t` and `t - w` lie in the same block at every scale
`k ≥ m` (`t` the centre, `4|w|_∞ ≤ L^m`). -/
theorem cs_blk_pair {m : ℕ} (hm : m ≤ N) {w : Lam d L N} (hw : 4 * supNorm w ≤ L ^ m)
    {k : ℕ} (hmk : m ≤ k) :
    blk k (csCentre d L N m) = blk k (csCentre d L N m - w) ∧
      blk k (csCentre d L N m - w) = 0 := by
  have e : csCentre d L N m - w - csCentre d L N m = -w := by abel
  have hw' : 4 * supNorm (csCentre d L N m - w - csCentre d L N m) ≤ L ^ m := by
    rw [e, supNorm_neg]; exact hw
  have h2 : blk k (csCentre d L N m - w) = 0 := cs_blk_ball hm hw' hmk
  exact ⟨by rw [cs_blk_centre hm hmk, h2], h2⟩

/-- **Distance to the boundary**: the ball of radius `L^m/4 - |w|_∞` around `t - w` lies in the
block `0` at every scale `k ≥ m`. -/
theorem cs_blk_ball' {m : ℕ} (hm : m ≤ N) {w z : Lam d L N}
    (hz : 4 * (supNorm (z - (csCentre d L N m - w)) + supNorm w) ≤ L ^ m) {k : ℕ}
    (hmk : m ≤ k) : blk k z = 0 := by
  refine cs_blk_ball hm ?_ hmk
  have e : z - csCentre d L N m = (z - (csCentre d L N m - w)) + -w := by abel
  have := FRD.supNorm_add_le (z - (csCentre d L N m - w)) (-w)
  rw [supNorm_neg] at this
  rw [e]; omega

/-- `|w|_∞ ≤ L^{m-r}`, `4 ≤ L^r`, `r ≤ m` give `4|w|_∞ ≤ L^m`. -/
theorem cs_four_le {m r : ℕ} (hrm : r ≤ m) (hLr : 4 ≤ L ^ r) {w : Lam d L N}
    (hw : supNorm w ≤ L ^ (m - r)) : 4 * supNorm w ≤ L ^ m := by
  have e : L ^ m = L ^ r * L ^ (m - r) := by rw [← pow_add, Nat.add_sub_cancel' hrm]
  rw [e]
  exact Nat.mul_le_mul hLr hw

/-! ### Coalescence scales -/

/-- **The coalescence scales of the shifted pairs**: `j_c(t, t + x) = j_c(0, x)` and
`j_c(t - (y - x), t + x) = j_c(0, y)`. -/
theorem cs_coal_eq (t x y : Lam d L N) :
    Obs.coal L t (t + x) = Obs.coal L (0 : Lam d L N) x ∧
      Obs.coal L (t - (y - x)) (t + x) = Obs.coal L (0 : Lam d L N) y := by
  unfold Obs.coal
  refine ⟨?_, ?_⟩
  · congr 2; congr 1; abel
  · congr 2; congr 1; abel

theorem cs_coal_zero (x : Lam d L N) : Obs.coal L (0 : Lam d L N) x = Nat.log L (2 * supNorm x) := by
  unfold Obs.coal; rw [zero_sub, supNorm_neg]

/-- **Coalescence at macroscopic distance**: `L^N ≤ L^c|x|_∞` gives `N - c ≤ j_c(0, x)` (`2 ≤ L`). -/
theorem cs_coal_ge (hL : 2 ≤ L) {c : ℕ} {x : Lam d L N} (hx : L ^ N ≤ L ^ c * supNorm x) :
    N - c ≤ Obs.coal L (0 : Lam d L N) x := by
  rw [cs_coal_zero]
  rcases le_or_gt c N with hcN | hcN
  · refine Nat.le_log_of_pow_le (by omega) ?_
    have e : L ^ N = L ^ c * L ^ (N - c) := by rw [← pow_add, Nat.add_sub_cancel' hcN]
    have hx' : L ^ c * L ^ (N - c) ≤ L ^ c * supNorm x := e ▸ hx
    have hpos : 0 < L ^ c := pow_pos (by omega) c
    have := Nat.le_of_mul_le_mul_left hx' hpos
    omega
  · rw [Nat.sub_eq_zero_of_le hcN.le]; exact Nat.zero_le _

/-- `m < j_c(0, x)` for `m + c < N`. -/
theorem cs_coal_gt (hL : 2 ≤ L) {c m : ℕ} (hmc : m + c < N) {x : Lam d L N}
    (hx : L ^ N ≤ L ^ c * supNorm x) : m < Obs.coal L (0 : Lam d L N) x := by
  have := cs_coal_ge hL hx; omega

/-- **The physical form**: `(L:ℝ)^{-c} ≤ δ` and `δ L^N ≤ |x|_∞` give `N - c ≤ j_c(0, x)`. -/
theorem cs_coal_ge_phys (hL : 2 ≤ L) {c : ℕ} {δ : ℝ} (hδ : ((L : ℝ) ^ c)⁻¹ ≤ δ)
    {x : Lam d L N} (hx : δ * (L : ℝ) ^ N ≤ supNorm x) :
    N - c ≤ Obs.coal L (0 : Lam d L N) x := by
  refine cs_coal_ge hL ?_
  have hLc : (0 : ℝ) < (L : ℝ) ^ c := by positivity
  have hLN : (0 : ℝ) ≤ (L : ℝ) ^ N := by positivity
  have h1 : ((L : ℝ) ^ c)⁻¹ * (L : ℝ) ^ N ≤ supNorm x :=
    le_trans (mul_le_mul_of_nonneg_right hδ hLN) hx
  have h2 : ((L ^ N : ℕ) : ℝ) ≤ ((L ^ c * supNorm x : ℕ) : ℝ) := by
    push_cast
    rw [inv_mul_le_iff₀ hLc] at h1; exact h1
  exact_mod_cast h2

end

end Spin2
