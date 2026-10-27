import Loc.PauliAbs
import FRD.BoundsLattice

/-!
# A smooth partition of unity on the torus (Lemma `lem:pauli`)

On `Λ = (ℤ/nℤ)^d`, at scale `R` with `R ∣ n`:

* `pathH_torus`: the path property `PathH` for the centre `c`, with
  `Dst(y) = ∑_i val((y - c)_i)` (walking in the positive coordinate directions);
* `box`, `bsp`: the indicator of the cube `[0, R)^d` and the discrete B-splines
  `bsp (m+1) = R^{-d} box ⋆ bsp m`;
* `sum_bsp_grid`: `∑_q bsp m (x - R q) = 1` (grid points `R q`, `q ∈ (ℤ/K)^d`, `K = n/R`);
* `sum_grid_D1_bsp_le`: `∑_q |∇^b bsp m (· - R q)| ≤ (2/R)^{|b|}` for `|b| ≤ m`;
* `bsp_support`: `bsp m t ≠ 0 → val t_i < (m+1) R`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n]

/-! ### Paths on the torus -/

theorem coord_sub_dirVec_inl (x : Torus d n) (i k : Fin d) :
    ((x - dirVec (Sum.inl i) : Torus d n) : Fin d → ZMod n) k =
      (x : Fin d → ZMod n) k - if k = i then 1 else 0 := by
  change (x : Fin d → ZMod n) k - (Pi.single i 1 : Fin d → ZMod n) k = _
  simp [Pi.single_apply]

/-- The distance of `y` from the centre `c` along positive paths. -/
def dstT (c : Torus d n) (y : Sf (Torus d n)) : ℕ :=
  ∑ i, (((y.1 - c : Torus d n) : Fin d → ZMod n) i).val

/-- The path property for the centre `c`. -/
theorem pathH_torus (hn : 1 < n) (c : Torus d n) :
    PathH (E := Dir d) (cenAt c) (fun y => (dstT c y : ℝ)) := by
  haveI : Fact (1 < n) := ⟨hn⟩
  intro φ K hK
  suffices H : ∀ s : ℕ, ∀ y : Sf (Torus d n), dstT c y = s → ‖φ y - φ (cenAt c y)‖ ≤ s * K by
    intro y; exact H _ y rfl
  intro s
  induction s with
  | zero =>
    intro y hy
    have h0 : ∀ i, (((y.1 - c : Torus d n) : Fin d → ZMod n) i).val = 0 := fun i =>
      (sum_eq_zero_iff.1 hy) i (mem_univ i)
    have hyc : y = cenAt c y := by
      refine Prod.ext ?_ rfl
      have : (y.1 - c : Torus d n) = 0 := by
        funext i; exact (ZMod.val_eq_zero _).1 (h0 i)
      simpa [cenAt, sub_eq_zero] using this
    rw [← hyc, sub_self, norm_zero]; simp
  | succ s ih =>
    intro y hy
    obtain ⟨i, hi⟩ : ∃ i, 1 ≤ (((y.1 - c : Torus d n) : Fin d → ZMod n) i).val := by
      by_contra h; push Not at h
      have : dstT c y = 0 := sum_eq_zero fun i _ => by have := h i; omega
      omega
    set y' : Sf (Torus d n) := (y.1 - dirVec (Sum.inl i), y.2)
    have hsh : sh (Pi.single (Sum.inl i : Dir d) 1 : Dir d → ℕ) y' = y := by
      simp only [sh, y', single_vadd, sub_add_cancel]
    have hy' : dstT c y' = s := by
      have e : ∀ k, (((y'.1 - c : Torus d n) : Fin d → ZMod n) k).val =
          (((y.1 - c : Torus d n) : Fin d → ZMod n) k).val - if k = i then 1 else 0 := by
        intro k
        have : ((y'.1 - c : Torus d n) : Fin d → ZMod n) k =
            ((y.1 - c : Torus d n) : Fin d → ZMod n) k - if k = i then 1 else 0 := by
          simp only [y', sub_right_comm _ (dirVec (Sum.inl i)) c]
          exact coord_sub_dirVec_inl _ i k
        rw [this]
        by_cases hk : k = i
        · subst hk
          rw [if_pos rfl, if_pos rfl, ZMod.val_sub (by rw [ZMod.val_one]; exact hi), ZMod.val_one]
        · rw [if_neg hk, if_neg hk, sub_zero, Nat.sub_zero]
      unfold dstT
      rw [sum_congr rfl fun k _ => e k]
      have hsum := Finset.sum_tsub_distrib (f := fun k => (((y.1 - c : Torus d n) : Fin d → ZMod n) k).val)
        (g := fun k => if k = i then 1 else 0) (s := univ) (fun k _ => by
          by_cases hk : k = i
          · subst hk; simpa using hi
          · simp [hk])
      rw [hsum, sum_ite_eq', if_pos (mem_univ _)]
      change dstT c y - 1 = s
      omega
    have hc : cenAt c y' = cenAt c y := rfl
    calc ‖φ y - φ (cenAt c y)‖ ≤ ‖φ y - φ y'‖ + ‖φ y' - φ (cenAt c y')‖ := by
          rw [hc]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ K + s * K := by
          refine add_le_add ?_ (ih y' hy')
          rw [← hsh]; exact hK y' _
      _ = ((s + 1 : ℕ) : ℝ) * K := by push_cast; ring


/-! ### One-dimensional facts -/

theorem card_val_lt {R : ℕ} (hR : R ≤ n) :
    ∑ t : ZMod n, (if t.val < R then (1 : ℝ) else 0) = R := by
  rw [sum_zmod_val (fun v => if v < R then (1 : ℝ) else 0), sum_boole]
  have : (range n).filter (fun v => v < R) = range R := by
    ext v; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

theorem val_sub_of_lt {a b : ZMod n} (h : a.val < b.val) : (a - b).val = n - b.val + a.val := by
  have h1 := ZMod.val_add (a - b) b
  rw [sub_add_cancel] at h1
  have hw := ZMod.val_lt (a - b)
  have hb := ZMod.val_lt b
  set w := (a - b).val
  have hk : (w + b.val) / n < 2 := by
    rw [Nat.div_lt_iff_lt_mul (NeZero.pos n)]; omega
  have hdm := Nat.div_add_mod (w + b.val) n
  rw [← h1] at hdm
  interval_cases hq : (w + b.val) / n <;> omega

/-- Exactly one grid point `R q` has `x - R q ∈ [0, R)`. -/
theorem sum_grid1 {R K : ℕ} (hR : 0 < R) (hn : n = R * K) (a : ZMod n) :
    ∑ q : Fin K, (if (a - ((R * q : ℕ) : ZMod n)).val < R then (1 : ℝ) else 0) = 1 := by
  have hav := ZMod.val_lt a
  obtain ⟨v, hv⟩ : ∃ v, v = a.val := ⟨_, rfl⟩
  rw [← hv] at hav
  have hdm := Nat.div_add_mod v R
  have hmod := Nat.mod_lt v hR
  have hq0 : v / R < K := by
    rw [Nat.div_lt_iff_lt_mul hR, mul_comm, ← hn]; exact hav
  have hRq : ∀ q : Fin K, R * q < n := fun q => by
    have := q.isLt
    calc R * q < R * K := Nat.mul_lt_mul_of_pos_left this hR
      _ = n := hn.symm
  have hRqv : ∀ q : Fin K, ((R * q : ℕ) : ZMod n).val = R * q :=
    fun q => ZMod.val_cast_of_lt (hRq q)
  rw [Finset.sum_eq_single (⟨v / R, hq0⟩ : Fin K)]
  · rw [if_pos]
    have hle : R * (v / R) ≤ v := Nat.mul_div_le v R
    rw [ZMod.val_sub (by rw [hRqv, ← hv]; exact hle), hRqv, ← hv]
    simp only
    omega
  · intro q _ hq
    rw [if_neg]
    by_cases hle : R * q ≤ v
    · rw [ZMod.val_sub (by rw [hRqv, ← hv]; exact hle), hRqv, ← hv]
      intro h
      apply hq
      ext
      simp only
      have h1 : v / R < q + 1 := by
        rw [Nat.div_lt_iff_lt_mul hR, mul_comm]; rw [mul_add, mul_one]; omega
      have h2 : q ≤ v / R := by
        rw [Nat.le_div_iff_mul_le hR, mul_comm]; exact hle
      omega
    · push Not at hle
      rw [val_sub_of_lt (by rw [hRqv, ← hv]; exact hle), hRqv, ← hv]
      have : R * q + R ≤ n := by
        rw [hn, ← mul_add_one]; exact Nat.mul_le_mul_left R q.isLt
      omega
  · intro h; exact absurd (mem_univ _) h


/-! ### Boxes and B-splines -/

variable (R : ℕ)

/-- The indicator of the cube `[0, R)^d`. -/
def box (t : Torus d n) : ℝ := ∏ i, if ((t : Fin d → ZMod n) i).val < R then 1 else 0

/-- The discrete B-splines: `bsp 0 = box`, `bsp (m+1) = R^{-d} box ⋆ bsp m`. -/
def bsp : ℕ → Torus d n → ℝ
  | 0 => box R
  | m + 1 => fun t => ((R : ℝ) ^ d)⁻¹ * ∑ s : Torus d n, box R s * bsp m (t - s)

/-- The grid point `R q`. -/
def gridPt {K : ℕ} (q : Fin d → Fin K) : Torus d n := fun i => ((R * q i : ℕ) : ZMod n)

variable {R}

theorem box_nonneg (t : Torus d n) : 0 ≤ box R t :=
  prod_nonneg fun i _ => by split_ifs <;> norm_num

theorem sum_prod_coord (f : Fin d → ZMod n → ℝ) :
    ∑ s : Torus d n, ∏ i, f i ((s : Fin d → ZMod n) i) = ∏ i, ∑ t : ZMod n, f i t :=
  (Fintype.prod_sum f).symm

theorem sum_box (hR : R ≤ n) : ∑ s : Torus d n, box R s = (R : ℝ) ^ d := by
  unfold box
  rw [sum_prod_coord (fun _ t => if t.val < R then (1 : ℝ) else 0)]
  simp only [card_val_lt hR, prod_const, card_univ, Fintype.card_fin]

theorem bsp_nonneg : ∀ (m : ℕ) (t : Torus d n), 0 ≤ bsp R m t
  | 0, t => box_nonneg t
  | m + 1, t => mul_nonneg (by positivity)
      (sum_nonneg fun s _ => mul_nonneg (box_nonneg s) (bsp_nonneg m _))

theorem coord_sub_gridPt {K : ℕ} (x : Torus d n) (q : Fin d → Fin K) (i : Fin d) :
    ((x - gridPt R q : Torus d n) : Fin d → ZMod n) i =
      (x : Fin d → ZMod n) i - ((R * q i : ℕ) : ZMod n) := rfl

/-- The B-splines translated to the grid points form a partition of unity. -/
theorem sum_bsp_grid (hR0 : 0 < R) {K : ℕ} (hn : n = R * K) :
    ∀ (m : ℕ) (x : Torus d n), ∑ q : Fin d → Fin K, bsp R m (x - gridPt R q) = 1
  | 0, x => by
    simp only [bsp, box, coord_sub_gridPt]
    exact (Fintype.prod_sum (fun i (qi : Fin K) =>
      if ((x : Fin d → ZMod n) i - ((R * qi : ℕ) : ZMod n)).val < R then (1 : ℝ) else 0)).symm.trans
      (prod_eq_one fun i _ => sum_grid1 hR0 hn _)
  | m + 1, x => by
    simp only [bsp]
    rw [← mul_sum, sum_comm]
    have : ∀ s : Torus d n, ∑ q : Fin d → Fin K, box R s * bsp R m (x - gridPt R q - s) =
        box R s := by
      intro s
      rw [← mul_sum]
      have e : ∀ q : Fin d → Fin K, x - gridPt R q - s = (x - s) - gridPt R q := fun q => by abel
      simp only [e, sum_bsp_grid hR0 hn m (x - s), mul_one]
    have hK : 0 < K := Nat.pos_of_ne_zero fun h => by
      subst h; simp at hn; exact NeZero.ne n hn
    rw [sum_congr rfl fun s _ => this s, sum_box (by rw [hn]; exact Nat.le_mul_of_pos_right R hK)]
    have hRd : ((R : ℝ) ^ d) ≠ 0 := by positivity
    exact inv_mul_cancel₀ hRd

/-- The convolution identity for differences. -/
theorem bsp_succ_sub (m : ℕ) (t v : Torus d n) :
    bsp R (m + 1) (t + v) - bsp R (m + 1) t =
      ((R : ℝ) ^ d)⁻¹ * ∑ s : Torus d n, (box R (s + v) - box R s) * bsp R m (t - s) := by
  have : ∑ s : Torus d n, box R s * bsp R m (t + v - s) =
      ∑ s : Torus d n, box R (s + v) * bsp R m (t - s) := by
    rw [← Equiv.sum_comp (Equiv.addRight v)]
    refine sum_congr rfl fun s _ => ?_
    simp only [Equiv.coe_addRight]
    congr 2; abel
  simp only [bsp]
  rw [← mul_sub, this, ← sum_sub_distrib]
  congr 1
  exact sum_congr rfl fun s _ => by ring

/-- The support of the B-splines. -/
theorem bsp_support : ∀ (m : ℕ) (t : Torus d n), bsp R m t ≠ 0 →
    ∀ i, ((t : Fin d → ZMod n) i).val < (m + 1) * R
  | 0, t, ht, i => by
    by_contra h
    push Not at h
    apply ht
    unfold bsp box
    exact prod_eq_zero (mem_univ i) (by rw [if_neg (by omega)])
  | m + 1, t, ht, i => by
    simp only [bsp] at ht
    obtain ⟨s, -, hs⟩ := exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul ht)
    have hbox : box R s ≠ 0 := left_ne_zero_of_mul hs
    have hb := bsp_support m (t - s) (right_ne_zero_of_mul hs) i
    have hsi : ((s : Fin d → ZMod n) i).val < R := by
      by_contra h; push Not at h
      apply hbox
      unfold box
      exact prod_eq_zero (mem_univ i) (by rw [if_neg (by omega)])
    have : ((t : Fin d → ZMod n) i) = ((t - s : Torus d n) : Fin d → ZMod n) i +
        (s : Fin d → ZMod n) i := by
      show _ = ((t : Fin d → ZMod n) i - (s : Fin d → ZMod n) i) + _; ring
    rw [this]
    calc _ ≤ _ := ZMod.val_add_le _ _
      _ < (m + 1) * R + R := by omega
      _ = (m + 1 + 1) * R := by ring


/-! ### Differences of the box -/

theorem sum_abs_dind_pos (hn : 1 < n) (R : ℕ) :
    ∑ t : ZMod n, |(if (t + 1).val < R then (1 : ℝ) else 0) - (if t.val < R then 1 else 0)| ≤ 2 := by
  haveI : Fact (1 < n) := ⟨hn⟩
  have e : ∀ t : ZMod n, (t + 1).val = (t.val + 1) % n := fun t => by
    rw [ZMod.val_add, ZMod.val_one]
  simp only [e]
  rw [sum_zmod_val (fun v => |(if (v + 1) % n < R then (1 : ℝ) else 0) - (if v < R then 1 else 0)|)]
  calc ∑ v ∈ range n, |(if (v + 1) % n < R then (1 : ℝ) else 0) - (if v < R then 1 else 0)|
      ≤ ∑ v ∈ range n, ((if v = R - 1 then (1 : ℝ) else 0) + (if v = n - 1 then 1 else 0)) := by
        refine sum_le_sum fun v hv => ?_
        rw [mem_range] at hv
        by_cases h1 : v + 1 < n
        · rw [Nat.mod_eq_of_lt h1]
          by_cases h2 : v = R - 1
          · split_ifs <;> norm_num
          · rw [if_neg h2]
            have : (v + 1 < R ↔ v < R) := by omega
            by_cases h3 : v < R
            · rw [if_pos h3, if_pos (this.2 h3)]; split_ifs <;> norm_num
            · rw [if_neg h3, if_neg (fun h => h3 (this.1 h))]; split_ifs <;> norm_num
        · have hv' : v = n - 1 := by omega
          rw [if_pos hv']
          split_ifs <;> norm_num
    _ ≤ 2 := by
        rw [sum_add_distrib, sum_ite_eq', sum_ite_eq']
        split_ifs <;> norm_num


theorem sum_abs_dind_neg (hn : 1 < n) (R : ℕ) :
    ∑ t : ZMod n, |(if (t + -1).val < R then (1 : ℝ) else 0) - (if t.val < R then 1 else 0)| ≤ 2 := by
  haveI : Fact (1 < n) := ⟨hn⟩
  have e : ∀ t : ZMod n, (t + -1).val = if t.val = 0 then n - 1 else t.val - 1 := by
    intro t
    rw [← sub_eq_add_neg]
    split_ifs with h
    · rw [val_sub_of_lt (by rw [h, ZMod.val_one]; norm_num), h, ZMod.val_one]; omega
    · rw [ZMod.val_sub (by rw [ZMod.val_one]; omega), ZMod.val_one]
  simp only [e]
  rw [sum_zmod_val (fun v => |(if (if v = 0 then n - 1 else v - 1) < R then (1 : ℝ) else 0) -
    (if v < R then 1 else 0)|)]
  calc ∑ v ∈ range n, |(if (if v = 0 then n - 1 else v - 1) < R then (1 : ℝ) else 0) -
          (if v < R then 1 else 0)|
      ≤ ∑ v ∈ range n, ((if v = 0 then (1 : ℝ) else 0) + (if v = R then 1 else 0)) := by
        refine sum_le_sum fun v hv => ?_
        by_cases h0 : v = 0
        · rw [if_pos h0, if_pos h0]; split_ifs <;> norm_num
        · rw [if_neg h0, if_neg h0, zero_add]
          by_cases h2 : v = R
          · split_ifs <;> norm_num
          · rw [if_neg h2]
            have : (v - 1 < R ↔ v < R) := by omega
            by_cases h3 : v < R
            · rw [if_pos h3, if_pos (this.2 h3)]; norm_num
            · rw [if_neg h3, if_neg (fun h => h3 (this.1 h))]; norm_num
    _ ≤ 2 := by
        rw [sum_add_distrib, sum_ite_eq', sum_ite_eq']
        split_ifs <;> norm_num

/-- The 1D indicator. -/
def ind1 (R : ℕ) (t : ZMod n) : ℝ := if t.val < R then 1 else 0

theorem box_eq (t : Torus d n) : box R t = ∏ i, ind1 R ((t : Fin d → ZMod n) i) := rfl

theorem ind1_nonneg (R : ℕ) (t : ZMod n) : 0 ≤ ind1 R t := by unfold ind1; split_ifs <;> norm_num

/-- `w e_i` as a vector of the torus. -/
def tvec (i : Fin d) (w : ZMod n) : Torus d n := (Pi.single i w : Fin d → ZMod n)

/-- `∑_s |box(s + w e_i) - box(s)| ≤ 2 R^{d-1}` if the 1D differences sum to `≤ 2`. -/
theorem sum_abs_dbox (hR : R ≤ n) (i : Fin d) (w : ZMod n)
    (h1 : ∑ t : ZMod n, |ind1 R (t + w) - ind1 R t| ≤ 2) :
    ∑ s : Torus d n, |box R (s + tvec i w) - box R s| ≤
      2 * (R : ℝ) ^ (d - 1) := by
  set F : Fin d → ZMod n → ℝ := fun j t => if j = i then |ind1 R (t + w) - ind1 R t| else ind1 R t
  have hpt : ∀ s : Torus d n, |box R (s + tvec i w) - box R s| =
      ∏ j, F j ((s : Fin d → ZMod n) j) := by
    intro s
    rw [box_eq, box_eq, ← Finset.mul_prod_erase univ _ (mem_univ i),
      ← Finset.mul_prod_erase univ _ (mem_univ i), ← Finset.mul_prod_erase univ _ (mem_univ i)]
    have hrest : ∏ j ∈ univ.erase i, ind1 R (((s + tvec i w : Torus d n) :
        Fin d → ZMod n) j) = ∏ j ∈ univ.erase i, ind1 R ((s : Fin d → ZMod n) j) := by
      refine prod_congr rfl fun j hj => ?_
      have hji := ne_of_mem_erase hj
      show ind1 R ((s : Fin d → ZMod n) j + (Pi.single i w : Fin d → ZMod n) j) = _
      rw [Pi.single_eq_of_ne hji, add_zero]
    have hF : ∏ j ∈ univ.erase i, F j ((s : Fin d → ZMod n) j) =
        ∏ j ∈ univ.erase i, ind1 R ((s : Fin d → ZMod n) j) :=
      prod_congr rfl fun j hj => by simp [F, ne_of_mem_erase hj]
    rw [hrest, hF, ← sub_mul, abs_mul,
      abs_of_nonneg (prod_nonneg fun j _ => ind1_nonneg R _)]
    congr 1
    show |ind1 R ((s : Fin d → ZMod n) i + (Pi.single i w : Fin d → ZMod n) i) - _| = F i _
    simp [F]
  rw [sum_congr rfl fun s _ => hpt s, sum_prod_coord F, ← Finset.mul_prod_erase univ _ (mem_univ i)]
  have hi : ∑ t, F i t ≤ 2 := by simpa [F] using h1
  have hj : ∀ j ∈ univ.erase i, ∑ t, F j t = R := fun j hj => by
    simp only [F, if_neg (ne_of_mem_erase hj)]
    exact card_val_lt hR
  rw [prod_congr rfl hj, prod_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right hi (by positivity)

theorem sum_abs_dbox_dir (hn : 1 < n) (hR : R ≤ n) (e : Dir d) :
    ∑ s : Torus d n, |box R (s + dirVec e) - box R s| ≤ 2 * (R : ℝ) ^ (d - 1) := by
  rcases e with i | i
  · exact sum_abs_dbox hR i 1 (sum_abs_dind_pos hn R)
  · have : (dirVec (Sum.inr i) : Torus d n) = (Pi.single i (-1) : Fin d → ZMod n) := by
      show -(Pi.single i 1 : Fin d → ZMod n) = _
      rw [Pi.single_neg]
    rw [this]
    exact sum_abs_dbox hR i (-1) (sum_abs_dind_neg hn R)


/-! ### Derivatives of the B-splines -/

theorem D1_sum' {ι : Type*} (S : Finset ι) (b : Dir d → ℕ) (c : ι → ℝ)
    (φ : ι → Sf (Torus d n) → ℝ) (y : Sf (Torus d n)) :
    D1 sh b (fun a => ∑ s ∈ S, c s * φ s a) y = ∑ s ∈ S, c s * D1 sh b (φ s) y := by
  simp only [D1_eq_sum, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun s _ => sum_congr rfl fun c' _ => by ring

theorem D1_translate (b : Dir d → ℕ) (φ : Torus d n → ℝ) (s : Torus d n) (y : Sf (Torus d n)) :
    D1 sh b (fun a => φ (a.1 - s)) y = D1 sh b (fun a => φ a.1) (y.1 - s, y.2) := by
  simp only [D1_eq_sum]
  refine sum_congr rfl fun c _ => ?_
  congr 2
  simp only [sh, vadd_def]
  abel

theorem D1_succ_torus (b : Dir d → ℕ) (e : Dir d) (φ : Torus d n → ℝ) (y : Sf (Torus d n)) :
    D1 sh (b + Pi.single e 1) (fun a => φ a.1) y =
      D1 sh b (fun a => φ (a.1 + dirVec e) - φ a.1) y := by
  rw [D1_succ _ sh_add']
  congr 1
  funext a
  simp [sh, single_vadd]

/-- `∑_q |∇^b bsp m (· - R q)| ≤ (2/R)^{|b|}` for `|b| ≤ m`. -/
theorem sum_grid_D1_bsp_le (hn1 : 1 < n) (hR0 : 0 < R) {K : ℕ} (hn : n = R * K) :
    ∀ (k : ℕ) (m : ℕ) (b : Dir d → ℕ), mabs b = k → k ≤ m → ∀ y : Sf (Torus d n),
      ∑ q : Fin d → Fin K, |D1 sh b (fun a => bsp R m (a.1 - gridPt R q)) y| ≤ (2 / R) ^ k := by
  have hRn : R ≤ n := by
    rw [hn]
    exact Nat.le_mul_of_pos_right R (Nat.pos_of_ne_zero fun h => by
      subst h; simp at hn; exact NeZero.ne n hn)
  intro k
  induction k with
  | zero =>
    intro m b hb _ y
    have hb0 : b = 0 := mabs_eq_zero hb
    subst hb0
    simp only [D1_zero _ sh_zero', pow_zero]
    rw [sum_congr rfl fun q _ => abs_of_nonneg (bsp_nonneg m _)]
    exact (sum_bsp_grid hR0 hn m y.1).le
  | succ k ih =>
    intro m b hb hkm y
    have hne : b ≠ 0 := by rintro rfl; simp [Grassmann.mabs] at hb
    obtain ⟨e, he⟩ : ∃ e, b e ≠ 0 := by
      by_contra h; push Not at h; exact hne (funext h)
    set b' := b - Pi.single e 1
    have hbb : b = b' + Pi.single e 1 := by
      funext e'
      by_cases he' : e' = e
      · subst he'; simp [b']; omega
      · simp [b', he']
    have hb' : mabs b' = k := by
      have := mabs_add b' (Pi.single e 1)
      rw [← hbb, mabs_single] at this; omega
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hbb]
    have hstep : ∀ q : Fin d → Fin K, D1 sh (b' + Pi.single e 1)
        (fun a => bsp R (m' + 1) (a.1 - gridPt R q)) y =
        ((R : ℝ) ^ d)⁻¹ * ∑ s : Torus d n, (box R (s + dirVec e) - box R s) *
          D1 sh b' (fun a => bsp R m' (a.1 - gridPt R q - s)) y := by
      intro q
      rw [D1_succ_torus b' e (fun x => bsp R (m' + 1) (x - gridPt R q)) y]
      have : (fun a : Sf (Torus d n) => bsp R (m' + 1) (a.1 + dirVec e - gridPt R q) -
          bsp R (m' + 1) (a.1 - gridPt R q)) = fun a => ((R : ℝ) ^ d)⁻¹ *
            ∑ s : Torus d n, (box R (s + dirVec e) - box R s) * bsp R m' (a.1 - gridPt R q - s) := by
        funext a
        rw [show a.1 + dirVec e - gridPt R q = (a.1 - gridPt R q) + dirVec e by abel, bsp_succ_sub]
      rw [this, show (fun a : Sf (Torus d n) => ((R : ℝ) ^ d)⁻¹ * ∑ s : Torus d n,
          (box R (s + dirVec e) - box R s) * bsp R m' (a.1 - gridPt R q - s)) =
          fun a => ∑ s ∈ univ, (((R : ℝ) ^ d)⁻¹ * (box R (s + dirVec e) - box R s)) *
            (fun s a => bsp R m' (a.1 - gridPt R q - s)) s a by
          funext a; rw [mul_sum]; exact sum_congr rfl fun s _ => by ring, D1_sum', mul_sum]
      exact sum_congr rfl fun s _ => by ring
    have hRd : (0 : ℝ) < (R : ℝ) ^ d := by positivity
    calc ∑ q : Fin d → Fin K, |D1 sh (b' + Pi.single e 1)
          (fun a => bsp R (m' + 1) (a.1 - gridPt R q)) y|
        ≤ ∑ q : Fin d → Fin K, ((R : ℝ) ^ d)⁻¹ * ∑ s : Torus d n, |box R (s + dirVec e) - box R s| *
            |D1 sh b' (fun a => bsp R m' (a.1 - gridPt R q - s)) y| := by
          refine sum_le_sum fun q _ => ?_
          rw [hstep, abs_mul, abs_of_pos (inv_pos.2 hRd)]
          refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (le_of_eq ?_))
            (by positivity)
          exact sum_congr rfl fun s _ => abs_mul _ _
      _ = ((R : ℝ) ^ d)⁻¹ * ∑ s : Torus d n, |box R (s + dirVec e) - box R s| *
            ∑ q : Fin d → Fin K, |D1 sh b' (fun a => bsp R m' (a.1 - gridPt R q - s)) y| := by
          rw [← mul_sum, sum_comm]
          congr 1
          exact sum_congr rfl fun s _ => by rw [mul_sum]
      _ ≤ ((R : ℝ) ^ d)⁻¹ * ∑ s : Torus d n, |box R (s + dirVec e) - box R s| * (2 / R) ^ k := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun s _ => ?_) (by positivity)
          refine mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_ (ih m' b' hb' (by omega) (y.1 - s, y.2)))
            (abs_nonneg _)
          refine sum_congr rfl fun q _ => ?_
          have e1 : (fun a : Sf (Torus d n) => bsp R m' (a.1 - gridPt R q - s)) =
              fun a => bsp R m' (a.1 - (s + gridPt R q)) := by funext a; congr 1; abel
          rw [e1, D1_translate (φ := bsp R m') (s := s + gridPt R q),
            D1_translate (φ := bsp R m') (s := gridPt R q)]
          congr 3
          simp only
          abel
      _ ≤ ((R : ℝ) ^ d)⁻¹ * (2 * (R : ℝ) ^ (d - 1)) * (2 / R) ^ k := by
          rw [← sum_mul, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (sum_abs_dbox_dir hn1 hRn e) (by positivity)
      _ = (2 / R) ^ (k + 1) := by
          have hd : 1 ≤ d := by
            rcases e with i | i <;> exact Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact i.elim0
          have hR' : (0 : ℝ) < R := by exact_mod_cast hR0
          rw [show (R : ℝ) ^ d = R ^ (d - 1) * R by rw [← pow_succ, Nat.sub_add_cancel hd], pow_succ]
          field_simp

end

end Loc
