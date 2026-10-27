import Step2.Map.LinB

/-!
# The number of blocks of a small set neighbourhood

`nb_nbhd_le`: `|𝓑_j(X^□)| ≤ (2^{d+1} + 3)^d |𝓑_j(X)|`. Points of `X^□` are within `2^d L^j` of
`X` (`exists_near_of_mem_nbhd`), so `X^□` is covered by `|𝓑_j(X)|` balls of radius
`(2^d + 1) L^j`, and `|X^□| = L^{jd} |𝓑_j(X^□)|`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

theorem card_ball_le (c : Lam d L N) (k : ℕ) :
    (univ.filter fun y : Lam d L N => supNorm (y - c) ≤ k).card ≤ (2 * k + 1) ^ d := by
  have h := card_supNorm_le (d := d) (n := L ^ N) k
  refine le_trans (le_of_eq ?_) h
  refine card_bij (fun y _ => y - c) (fun y hy => by simpa using hy)
    (fun y _ y' _ h => by simpa using h) fun x hx => ⟨x + c, by simpa using hx, by simp⟩

theorem nb_nbhd_le {j : ℕ} (hj : j ≤ N) (X : Finset (Lam d L N)) :
    nb j (nbhd j X) ≤ (2 ^ (d + 1) + 3) ^ d * nb j X := by
  classical
  have hR : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  -- a point of each block
  have hpt : ∀ b ∈ blocks j X, ∃ x ∈ X, blk j x = b := fun b hb => mem_image.1 hb
  choose pt hptX hptb using hpt
  set k := (2 ^ d + 1) * L ^ j
  have hcov : nbhd j X ⊆ (blocks j X).attach.biUnion fun b =>
      univ.filter fun y : Lam d L N => supNorm (y - pt b.1 b.2) ≤ k := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := exists_near_of_mem_nbhd hy
    have hb : blk j x ∈ blocks j X := blk_mem_blocks hx
    refine mem_biUnion.2 ⟨⟨blk j x, hb⟩, mem_attach _ _, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
    have h1 : supNorm (x - pt (blk j x) hb) < L ^ j :=
      supNorm_lt_of_blk_eq (hptb _ hb).symm
    have := supNorm_add_le (y - x) (x - pt (blk j x) hb)
    rw [sub_add_sub_cancel] at this
    simp only [k]
    nlinarith
  have hcard : (nbhd j X).card ≤ nb j X * (2 * k + 1) ^ d := by
    refine (card_le_card hcov).trans (card_biUnion_le.trans ?_)
    calc ∑ b ∈ (blocks j X).attach, (univ.filter fun y : Lam d L N =>
          supNorm (y - pt b.1 b.2) ≤ k).card
        ≤ ∑ _b ∈ (blocks j X).attach, (2 * k + 1) ^ d :=
          sum_le_sum fun b _ => card_ball_le _ _
      _ = nb j X * (2 * k + 1) ^ d := by rw [sum_const, card_attach, smul_eq_mul]; rfl
  have hpoly := isPolymer_nbhd j X
  have hc : (nbhd j X).card = nb j (nbhd j X) * L ^ (j * d) := by
    rw [card_polymer hpoly, sum_congr rfl fun b hb =>
      card_blockSet hj (mem_blockIdx_of_mem_blocks hb), sum_const, smul_eq_mul]
    rfl
  have h2k : 2 * k + 1 ≤ (2 ^ (d + 1) + 3) * L ^ j := by
    simp only [k]; rw [pow_succ]; nlinarith
  have h3 : nb j (nbhd j X) * L ^ (j * d) ≤ (2 ^ (d + 1) + 3) ^ d * nb j X * L ^ (j * d) := by
    rw [← hc]
    refine hcard.trans ?_
    calc nb j X * (2 * k + 1) ^ d ≤ nb j X * ((2 ^ (d + 1) + 3) * L ^ j) ^ d := by gcongr
      _ = (2 ^ (d + 1) + 3) ^ d * nb j X * L ^ (j * d) := by rw [mul_pow, ← pow_mul]; ring
  exact Nat.le_of_mul_le_mul_right h3 (pow_pos hR d |>.trans_eq (by rw [← pow_mul]))

/-! ### Points at distance `< L^k` lie in touching `k`-blocks -/

/-- One coordinate, upward case. -/
theorem val_one_le {n : ℕ} : (1 : ZMod n).val ≤ 1 := by
  rcases n with _ | n
  · simp [ZMod.val]
  · rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_le _ _

theorem coord_touch_up {n m K : ℕ} [NeZero n] (hm : 0 < m) (hK : 0 < K) (hnmK : n = m * K)
    (a b : ZMod n) (hδ : (b - a).val < m) :
    ∃ p q : ZMod n, p.val / m = a.val / m ∧ q.val / m = b.val / m ∧ zabs (q - p) ≤ 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set δ := (b - a).val
  have hb : b = a + ((b - a : ZMod n)) := by ring
  have hav := ZMod.val_lt a
  have hbv := ZMod.val_lt b
  have hbval : b.val = (a.val + δ) % n := by
    conv_lhs => rw [hb]
    rw [ZMod.val_add]
  by_cases heq : a.val / m = b.val / m
  · exact ⟨a, a, rfl, heq ▸ rfl, by simp [zabs]⟩
  set c := a.val / m
  by_cases hw : a.val + δ < n
  · rw [Nat.mod_eq_of_lt hw] at hbval
    have h1 : a.val < (c + 1) * m := by
      have := Nat.lt_div_mul_add hm (a := a.val); simp only [c]; nlinarith [Nat.div_mul_le_self a.val m]
    have h2 : c * m ≤ a.val := Nat.div_mul_le_self a.val m
    have hbc : b.val / m = c + 1 := by
      have hlt : b.val < (c + 2) * m := by rw [hbval]; nlinarith
      have hge : c ≤ b.val / m := by rw [hbval]; exact Nat.div_le_div_right (by omega)
      have hle : b.val / m < c + 2 := by rw [Nat.div_lt_iff_lt_mul hm]; exact hlt
      omega
    have hcm : (c + 1) * m ≤ b.val := by
      have := Nat.div_mul_le_self b.val m; rw [hbc] at this; exact this
    refine ⟨(((c + 1) * m - 1 : ℕ) : ZMod n), (((c + 1) * m : ℕ) : ZMod n), ?_, ?_, ?_⟩
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      have : (c + 1) * m - 1 = c * m + (m - 1) := by rw [add_mul, one_mul]; omega
      rw [this, Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt (by omega)]
      simp [c]
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), Nat.mul_div_cancel _ hm, hbc]
    · have e : (((c + 1) * m : ℕ) : ZMod n) - (((c + 1) * m - 1 : ℕ) : ZMod n) = 1 := by
        rw [Nat.cast_sub (by nlinarith), Nat.cast_one]; ring
      rw [e]
      unfold zabs
      exact (min_le_left _ _).trans val_one_le
  · push Not at hw
    have hδm := hδ
    have hmn : m ≤ n := by rw [hnmK]; exact Nat.le_mul_of_pos_right m hK
    have hbsmall : b.val < m := by
      rw [hbval, Nat.mod_eq_sub_mod hw, Nat.mod_eq_of_lt (by omega)]; omega
    have hb0 : b.val / m = 0 := Nat.div_eq_of_lt hbsmall
    have hac : c = K - 1 := by
      have h1 : (K - 1) * m ≤ a.val := by
        have : (K - 1) * m = n - m := by rw [hnmK, Nat.sub_mul, one_mul, mul_comm]
        omega
      have h2 : a.val < K * m := by rw [mul_comm, ← hnmK]; exact hav
      have hge : K - 1 ≤ c := (Nat.le_div_iff_mul_le hm).2 h1
      have hlt : c < K := (Nat.div_lt_iff_lt_mul hm).2 h2
      omega
    refine ⟨((n - 1 : ℕ) : ZMod n), 0, ?_, ?_, ?_⟩
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), hac]
      have : n - 1 = (K - 1) * m + (m - 1) := by
        rw [hnmK, Nat.sub_mul, one_mul, mul_comm m K]
        have : m ≤ K * m := Nat.le_mul_of_pos_left m hK
        omega
      rw [this, Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt (by omega)]
      simp
    · rw [ZMod.val_zero, Nat.zero_div, hb0]
    · have e : (0 : ZMod n) - ((n - 1 : ℕ) : ZMod n) = 1 := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring
      rw [e]
      unfold zabs
      exact (min_le_left _ _).trans val_one_le

theorem coord_touch {n m K : ℕ} [NeZero n] (hm : 0 < m) (hK : 0 < K) (hnmK : n = m * K)
    (a b : ZMod n) (h : zabs (b - a) < m) :
    ∃ p q : ZMod n, p.val / m = a.val / m ∧ q.val / m = b.val / m ∧ zabs (q - p) ≤ 1 := by
  unfold zabs at h
  rcases min_lt_iff.1 h with h' | h'
  · exact coord_touch_up hm hK hnmK a b h'
  · have h2 : (a - b).val < m := by
      have e : a - b = -(b - a) := by ring
      rw [e, ZMod.neg_val]
      split_ifs <;> omega
    obtain ⟨p, q, hp, hq, hpq⟩ := coord_touch_up hm hK hnmK b a h2
    refine ⟨q, p, hq, hp, ?_⟩
    rw [show p - q = -(q - p) by ring, zabs_neg]
    exact hpq

theorem touch_blocks_of_close {k : ℕ} (hk : k ≤ N) {x z : Lam d L N}
    (h : supNorm (z - x) < L ^ k) :
    Touch (blockSet (L := L) (N := N) k (blk k x)) (blockSet k (blk k z)) := by
  have hm : 0 < L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k
  have hK : 0 < L ^ (N - k) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hn : L ^ N = L ^ k * L ^ (N - k) := by rw [← pow_add, Nat.add_sub_cancel' hk]
  have hc : ∀ i : Fin d, ∃ p q : ZMod (L ^ N), p.val / L ^ k = ((x : Fin d → ZMod (L ^ N)) i).val / L ^ k ∧
      q.val / L ^ k = ((z : Fin d → ZMod (L ^ N)) i).val / L ^ k ∧ zabs (q - p) ≤ 1 := by
    intro i
    refine coord_touch hm hK hn _ _ (lt_of_le_of_lt ?_ h)
    exact (supNorm_le_iff (z - x) _).1 le_rfl i
  choose p q hp hq hpq using hc
  refine ⟨(p : Fin d → ZMod (L ^ N)), mem_blockSet.2 ?_, (q : Fin d → ZMod (L ^ N)),
    mem_blockSet.2 ?_, ?_⟩
  · funext i; exact hp i
  · funext i; exact hq i
  · refine (supNorm_le_iff _ _).2 fun i => ?_
    show zabs (p i - q i) ≤ 1
    rw [show p i - q i = -(q i - p i) by ring, zabs_neg]
    exact hpq i

/-- A point within `L^k` of a `k`-polymer `Y` lies in `Y^□` (at scale `k`). -/
theorem mem_nbhd_of_close (hd : 1 ≤ d) {k : ℕ} (hk : k ≤ N) {Y : Finset (Lam d L N)}
    {y z : Lam d L N} (hy : y ∈ Y) (hz : supNorm (z - y) < L ^ k) : z ∈ nbhd k Y := by
  classical
  set S : Finset (Lam d L N) := blockSet k (blk k y) ∪ blockSet k (blk k z) with hSdef
  have hbS : blocks k S ⊆ {blk k y, blk k z} := by
    intro b hb
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hb
    rcases mem_union.1 hw with hw | hw
    · simp [mem_blockSet.1 hw]
    · simp [mem_blockSet.1 hw]
  have hyS : y ∈ S := mem_union_left _ (mem_blockSet_blk k y)
  have hzS : z ∈ S := mem_union_right _ (mem_blockSet_blk k z)
  have ht := touch_blocks_of_close hk hz
  have hadj : ∀ b ∈ blocks k S, ∀ b' ∈ blocks k S, BlockAdj k S b b' := by
    intro b hb b' hb'
    refine ⟨hb, hb', ?_⟩
    rcases mem_insert.1 (hbS hb) with rfl | h1 <;>
      rcases mem_insert.1 (hbS hb') with rfl | h2
    · exact ⟨y, mem_blockSet_blk k y, y, mem_blockSet_blk k y, by simp [supNorm_zero]⟩
    · rw [mem_singleton.1 h2]; exact ht
    · rw [mem_singleton.1 h1]; exact touch_symm ht
    · rw [mem_singleton.1 h1, mem_singleton.1 h2]
      exact ⟨z, mem_blockSet_blk k z, z, mem_blockSet_blk k z, by simp [supNorm_zero]⟩
  have hsmall : IsSmall k S := by
    refine ⟨?_, ⟨⟨y, hyS⟩, fun b hb b' hb' => Relation.ReflTransGen.single (hadj b hb b' hb')⟩,
      ?_⟩
    · intro w w' hww' hw
      rcases mem_union.1 hw with hw | hw
      · exact mem_union_left _ (mem_blockSet.2 (hww'.symm.trans (mem_blockSet.1 hw)))
      · exact mem_union_right _ (mem_blockSet.2 (hww'.symm.trans (mem_blockSet.1 hw)))
    · refine (card_le_card hbS).trans ((card_insert_le _ _).trans ?_)
      simp only [card_singleton]
      calc 1 + 1 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  simp only [nbhd, mem_filter, mem_univ, true_and]
  exact ⟨S, hsmall, hzS, blk k y, blk_mem_blocks hy, subset_union_left⟩

/-! ### The interaction range of a block -/

open Classical in
/-- The blocks `B'` whose neighbourhood is within `L^{j+1}/2` of that of `B`. -/
def nearSet (j : ℕ) (b : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  (blockIdx (L := L) (N := N) j).filter fun b' =>
    ∃ x ∈ nbhd j (blockSet (L := L) (N := N) j b), ∃ y ∈ nbhd j (blockSet (L := L) (N := N) j b'),
      2 * supNorm (x - y) < L ^ (j + 1)

theorem supNorm_le_of_mem_nbhd_blockSet {j : ℕ} {b : Fin d → ℕ} {y z : Lam d L N}
    (hy : y ∈ nbhd j (blockSet (L := L) (N := N) j b)) (hz : z ∈ blockSet (L := L) (N := N) j b) :
    supNorm (y - z) ≤ (2 ^ d + 1) * L ^ j := by
  obtain ⟨x, hx, hyx⟩ := exists_near_of_mem_nbhd hy
  have h1 := supNorm_lt_of_blk_eq ((mem_blockSet.1 hx).trans (mem_blockSet.1 hz).symm)
  have := supNorm_add_le (y - x) (x - z)
  rw [sub_add_sub_cancel] at this
  nlinarith

theorem card_nearSet_le {j : ℕ} (hj : j ≤ N) (b : Fin d → ℕ)
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    (nearSet (L := L) (N := N) j b).card ≤ (L + 2 ^ (d + 3) + 7) ^ d := by
  classical
  have hR : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  obtain ⟨c, -, hc⟩ := mem_image.1 hb
  have hcB : c ∈ blockSet (L := L) (N := N) j b := mem_blockSet.2 hc
  set ρ := L ^ (j + 1) / 2 + (2 ^ (d + 1) + 3) * L ^ j
  have hsub : (nearSet (L := L) (N := N) j b).biUnion (blockSet j) ⊆
      univ.filter fun z : Lam d L N => supNorm (z - c) ≤ ρ := by
    intro z hz
    obtain ⟨b', hb', hzb'⟩ := mem_biUnion.1 hz
    obtain ⟨-, x, hx, y, hy, hxy⟩ := mem_filter.1 hb'
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    have h1 := supNorm_le_of_mem_nbhd_blockSet hy hzb'
    have h2 := supNorm_le_of_mem_nbhd_blockSet hx hcB
    have e : z - c = (z - y) + ((y - x) + (x - c)) := by abel
    have h3 := supNorm_add_le (z - y) ((y - x) + (x - c))
    have h4 := supNorm_add_le (y - x) (x - c)
    rw [← e] at h3
    rw [supNorm_sub_comm] at h1
    rw [supNorm_sub_comm y x] at h4
    have : supNorm (x - y) ≤ L ^ (j + 1) / 2 := by omega
    simp only [ρ]
    have hd2 : (2 ^ (d + 1) + 3) * L ^ j = (2 ^ d + 1) * L ^ j + ((2 ^ d + 1) * L ^ j + L ^ j) := by
      rw [pow_succ]; ring
    omega
  have hcard := (card_le_card hsub).trans (card_ball_le c ρ)
  rw [card_biUnion fun b₁ _ b₂ _ hne => blockSet_disjoint hne] at hcard
  have hc2 : ∑ u ∈ nearSet (L := L) (N := N) j b, (blockSet (L := L) (N := N) j u).card =
      (nearSet (L := L) (N := N) j b).card * L ^ (j * d) := by
    rw [sum_congr rfl (g := fun _ => L ^ (j * d)) fun u hu =>
      card_blockSet hj (by unfold nearSet at hu; exact (mem_filter.1 hu).1), sum_const,
      smul_eq_mul]
  rw [hc2] at hcard
  have h2ρ : 2 * ρ + 1 ≤ (L + 2 ^ (d + 3) + 7) * L ^ j := by
    have ht : 2 * (L ^ (j + 1) / 2) ≤ L * L ^ j := by
      have := Nat.mul_div_le (L ^ (j + 1)) 2
      rw [pow_succ, mul_comm (L ^ j) L] at this ⊢
      exact this
    have h8 : 2 ^ (d + 3) = 4 * 2 ^ (d + 1) := by
      rw [show d + 3 = (d + 1) + 2 by ring, pow_add]; ring
    have e1 : (L + 2 ^ (d + 3) + 7) * L ^ j = L * L ^ j + 4 * (2 ^ (d + 1) * L ^ j) + 7 * L ^ j := by
      rw [h8]; ring
    have e2 : 2 * ρ + 1 = 2 * (L ^ (j + 1) / 2) + 2 * (2 ^ (d + 1) * L ^ j) + 6 * L ^ j + 1 := by
      simp only [ρ]; ring
    rw [e1, e2]
    have : 0 ≤ 2 ^ (d + 1) * L ^ j := Nat.zero_le _
    linarith
  have h3 : (nearSet (L := L) (N := N) j b).card * L ^ (j * d) ≤
      (L + 2 ^ (d + 3) + 7) ^ d * L ^ (j * d) := by
    refine hcard.trans ((Nat.pow_le_pow_left h2ρ d).trans (le_of_eq ?_))
    rw [mul_pow, ← pow_mul, mul_comm j d]
  exact Nat.le_of_mul_le_mul_right h3 (pow_pos hR d |>.trans_eq (by rw [← pow_mul]))

theorem not_near_far {j : ℕ} {b b' : Fin d → ℕ} (hb' : b' ∈ blockIdx (L := L) (N := N) j)
    (h : b' ∉ nearSet (L := L) (N := N) j b) {x y : Lam d L N}
    (hx : x ∈ nbhd j (blockSet (L := L) (N := N) j b))
    (hy : y ∈ nbhd j (blockSet (L := L) (N := N) j b')) :
    L ^ (j + 1) ≤ 2 * supNorm (x - y) := by
  classical
  by_contra hc
  push Not at hc
  exact h (mem_filter.2 ⟨hb', x, hx, y, hy, hc⟩)

theorem mem_nbhd_succ_of_near (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 1 ≤ N)
    {b b' : Fin d → ℕ} (hb' : b' ∈ nearSet (L := L) (N := N) j b) {y : Lam d L N}
    (hy : y ∈ nbhd j (blockSet (L := L) (N := N) j b')) :
    y ∈ nbhd (j + 1) (clo j (blockSet (L := L) (N := N) j b)) := by
  classical
  obtain ⟨-, x, hx, y0, hy0, hxy⟩ := mem_filter.1 hb'
  obtain ⟨x1, hx1, hxx1⟩ := exists_near_of_mem_nbhd hx
  obtain ⟨z, hz, hy0z⟩ := exists_near_of_mem_nbhd hy0
  have h1 := supNorm_le_of_mem_nbhd_blockSet hy hz
  refine mem_nbhd_of_close hd hj (subset_clo j _ hx1) ?_
  have e : y - x1 = (y - z) + ((z - y0) + ((y0 - x) + (x - x1))) := by abel
  have h2 := supNorm_add_le (y - z) ((z - y0) + ((y0 - x) + (x - x1)))
  have h3 := supNorm_add_le (z - y0) ((y0 - x) + (x - x1))
  have h4 := supNorm_add_le (y0 - x) (x - x1)
  rw [← e] at h2
  rw [supNorm_sub_comm z y0] at h3
  rw [supNorm_sub_comm y0 x] at h4
  have hR1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  set R := L ^ j
  set u := 2 ^ d * R
  have hu : (2 ^ d + 1) * R = u + R := by simp only [u]; ring
  rw [hu] at h1
  have huR : R ≤ u := Nat.le_mul_of_pos_left R hR1
  have h8 : 8 * u ≤ L ^ (j + 1) := by
    have h83 : 2 ^ (d + 3) = 8 * 2 ^ d := by rw [pow_add]; ring
    rw [pow_succ, mul_comm (L ^ j) L]
    simp only [u, R]
    calc 8 * (2 ^ d * L ^ j) = 2 ^ (d + 3) * L ^ j := by rw [h83]; ring
      _ ≤ L * L ^ j := Nat.mul_le_mul_right _ hL
  omega

end

end Step2
