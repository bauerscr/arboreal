import Loc.Polymer

/-!
# Geometry of polymers and small sets

Elementary geometric facts about blocks, small sets and the small set neighbourhood `X^□`:

* points of one `j`-block are at sup-distance `< L^j`;
* single blocks are small sets, and `X ⊆ X^□`;
* small sets have sup-diameter `≤ 2^d L^j`, and `X^□` lies within `2^{d+1} L^j` of `X`;
* nearest neighbours of a polymer lie in its small set neighbourhood;
* `X ↦ X^□` is monotone.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d L N : ℕ} [NeZero L]

theorem mem_blockSet {j : ℕ} {b : Fin d → ℕ} {x : Lam d L N} :
    x ∈ blockSet j b ↔ blk j x = b := by
  simp [blockSet]

theorem mem_blockSet_blk (j : ℕ) (x : Lam d L N) : x ∈ blockSet j (blk j x) :=
  mem_blockSet.2 rfl

theorem blk_mem_blocks {j : ℕ} {X : Finset (Lam d L N)} {x : Lam d L N} (hx : x ∈ X) :
    blk j x ∈ blocks j X :=
  mem_image_of_mem _ hx

/-- points of one `j`-block are at sup-distance `< L^j` -/
theorem supNorm_lt_of_blk_eq {j : ℕ} {x y : Lam d L N} (h : blk j x = blk j y) :
    supNorm (x - y) < L ^ j := by
  have hP : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  suffices supNorm (x - y) ≤ L ^ j - 1 by omega
  rw [supNorm_le_iff]
  intro i
  have hi := congrFun h i
  simp only [blk] at hi
  have key : ((x - y : Lam d L N) : Fin d → ZMod (L ^ N)) i
      = ((((co x i).val : ℤ) - ((co y i).val : ℤ) : ℤ) : ZMod (L ^ N)) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rfl
  rw [key]
  refine (zabs_le_natAbs _).trans ?_
  have ha := Nat.div_add_mod (co x i).val (L ^ j)
  have hb := Nat.div_add_mod (co y i).val (L ^ j)
  have ha' := Nat.mod_lt (co x i).val hP
  have hb' := Nat.mod_lt (co y i).val hP
  rw [hi] at ha
  generalize L ^ j * ((co y i).val / L ^ j) = t at ha hb
  generalize (co x i).val % L ^ j = r at ha ha'
  generalize (co y i).val % L ^ j = s at hb hb'
  generalize (co x i).val = a at ha
  generalize (co y i).val = b at hb
  generalize L ^ j = P at *
  omega

/-- a single block (as a polymer) is a small set when it is nonempty -/
theorem isSmall_blockSet (j : ℕ) (x : Lam d L N) :
    IsSmall j (blockSet (L := L) (N := N) j (blk j x)) := by
  have hb : blocks (L := L) (N := N) j (blockSet j (blk j x)) ⊆ {blk j x} := by
    intro b hb
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hb
    exact mem_singleton.2 (mem_blockSet.1 hy)
  refine ⟨?_, ⟨⟨x, mem_blockSet_blk j x⟩, ?_⟩, ?_⟩
  · intro y z hyz hy
    exact mem_blockSet.2 (hyz.symm.trans (mem_blockSet.1 hy))
  · intro b hb' b' hb''
    rw [mem_singleton.1 (hb hb'), mem_singleton.1 (hb hb'')]
  · exact (card_le_card hb).trans (by simp [Nat.one_le_two_pow])

/-- X ⊆ X^□ for polymers -/
theorem subset_nbhd {j : ℕ} {X : Finset (Lam d L N)} (_hX : IsPolymer j X) : X ⊆ nbhd j X := by
  intro x hx
  simp only [nbhd, mem_filter, mem_univ, true_and]
  exact ⟨_, isSmall_blockSet j x, mem_blockSet_blk j x, blk j x, blk_mem_blocks hx,
    subset_refl _⟩

/-- The graph of touching blocks of `X`. -/
def blockGraph (j : ℕ) (X : Finset (Lam d L N)) : SimpleGraph {b // b ∈ blocks j X} :=
  SimpleGraph.fromRel fun b b' => Touch (blockSet (L := L) (N := N) j b.1) (blockSet j b'.1)

theorem reachable_of_reflTransGen {j : ℕ} {X : Finset (Lam d L N)} {b b' : Fin d → ℕ}
    (h : Relation.ReflTransGen (BlockAdj j X) b b') :
    ∀ (hb : b ∈ blocks j X) (hb' : b' ∈ blocks j X),
      (blockGraph j X).Reachable ⟨b, hb⟩ ⟨b', hb'⟩ := by
  induction h with
  | refl => intro hb hb'; rfl
  | @tail c e _ hce ih =>
    intro hb he
    refine (ih hb hce.1).trans ?_
    by_cases hne : c = e
    · subst hne; rfl
    · refine SimpleGraph.Adj.reachable ?_
      rw [blockGraph, SimpleGraph.fromRel_adj]
      exact ⟨fun h => hne (congrArg Subtype.val h), Or.inl hce.2.2⟩

theorem supNorm_add_one_le_of_walk {j : ℕ} {X : Finset (Lam d L N)}
    {u v : {b // b ∈ blocks j X}} (p : (blockGraph j X).Walk u v) {x z : Lam d L N}
    (hx : x ∈ blockSet j u.1) (hz : z ∈ blockSet j v.1) :
    supNorm (z - x) + 1 ≤ (p.length + 1) * L ^ j := by
  induction p generalizing x with
  | nil =>
    have := supNorm_lt_of_blk_eq ((mem_blockSet.1 hz).trans (mem_blockSet.1 hx).symm)
    simp only [SimpleGraph.Walk.length_nil, zero_add, one_mul]
    omega
  | @cons u w v h p ih =>
    rw [blockGraph, SimpleGraph.fromRel_adj] at h
    have touch : ∃ a : Lam d L N, a ∈ blockSet j u.1 ∧ ∃ a' : Lam d L N, a' ∈ blockSet j w.1 ∧ supNorm (a' - a) ≤ 1 := by
      rcases h.2 with ⟨a, ha, a', ha', h'⟩ | ⟨a', ha', a, ha, h'⟩
      · exact ⟨a, ha, a', ha', by rwa [supNorm_sub_comm]⟩
      · exact ⟨a, ha, a', ha', h'⟩
    obtain ⟨a, ha, a', ha', haa⟩ := touch
    have h1 : supNorm (z - a') + 1 ≤ (p.length + 1) * L ^ j := ih ha' hz
    have h2 := supNorm_lt_of_blk_eq ((mem_blockSet.1 ha).trans (mem_blockSet.1 hx).symm)
    have e : z - x = (z - a') + ((a' - a) + (a - x)) := by abel
    have h3 := supNorm_add_le (z - a') ((a' - a) + (a - x))
    have h4 := supNorm_add_le (a' - a) (a - x)
    rw [SimpleGraph.Walk.length_cons, add_mul, one_mul, e]
    omega

/-- diameter of small sets -/
theorem supNorm_le_of_isSmall {j : ℕ} {X : Finset (Lam d L N)} (hX : IsSmall j X)
    {x y : Lam d L N} (hx : x ∈ X) (hy : y ∈ X) : supNorm (x - y) ≤ 2 ^ d * L ^ j := by
  classical
  obtain ⟨-, ⟨-, hconn⟩, hcard⟩ := hX
  have hbx := blk_mem_blocks (j := j) hx
  have hby := blk_mem_blocks (j := j) hy
  obtain ⟨p, hp⟩ := (reachable_of_reflTransGen (hconn _ hby _ hbx) hby hbx).exists_isPath
  have hlen := hp.length_lt
  rw [Fintype.card_coe] at hlen
  have := supNorm_add_one_le_of_walk p (mem_blockSet_blk j y) (mem_blockSet_blk j x)
  calc supNorm (x - y) ≤ (p.length + 1) * L ^ j := by omega
    _ ≤ 2 ^ d * L ^ j := Nat.mul_le_mul_right _ (by omega)

/-- size of the small set neighbourhood -/
theorem supNorm_le_of_mem_nbhd {j : ℕ} {X : Finset (Lam d L N)} (hX : IsSmall j X)
    {x y : Lam d L N} (hx : x ∈ X) (hy : y ∈ nbhd j X) :
    supNorm (y - x) ≤ 2 ^ (d + 1) * L ^ j := by
  simp only [nbhd, mem_filter, mem_univ, true_and] at hy
  obtain ⟨S, hS, hyS, b, hb, hbS⟩ := hy
  obtain ⟨x₀, hx₀, rfl⟩ := mem_image.1 hb
  have h1 := supNorm_le_of_isSmall hS hyS (hbS (mem_blockSet_blk j x₀))
  have h2 := supNorm_le_of_isSmall hX hx₀ hx
  have e : y - x = (y - x₀) + (x₀ - x) := by abel
  rw [e, pow_succ, mul_comm (2 ^ d) 2, mul_assoc, two_mul]
  exact (supNorm_add_le _ _).trans (add_le_add h1 h2)

/-- nearest neighbours of a polymer lie in its small set neighbourhood (d ≥ 1) -/
theorem mem_nbhd_of_near {j : ℕ} (hd : 1 ≤ d) {Y : Finset (Lam d L N)} (_hY : IsPolymer j Y)
    {y z : Lam d L N} (hy : y ∈ Y) (hz : supNorm (z - y) ≤ 1) : z ∈ nbhd j Y := by
  classical
  set S : Finset (Lam d L N) := blockSet j (blk j y) ∪ blockSet j (blk j z) with hSdef
  have hbS : blocks j S ⊆ {blk j y, blk j z} := by
    intro b hb
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hb
    rcases mem_union.1 hw with hw | hw
    · simp [mem_blockSet.1 hw]
    · simp [mem_blockSet.1 hw]
  have hyS : y ∈ S := mem_union_left _ (mem_blockSet_blk j y)
  have hzS : z ∈ S := mem_union_right _ (mem_blockSet_blk j z)
  have hadj : ∀ b ∈ blocks j S, ∀ b' ∈ blocks j S, BlockAdj j S b b' := by
    intro b hb b' hb'
    refine ⟨hb, hb', ?_⟩
    rcases mem_insert.1 (hbS hb) with rfl | h1 <;>
      rcases mem_insert.1 (hbS hb') with rfl | h2
    · exact ⟨y, mem_blockSet_blk j y, y, mem_blockSet_blk j y, by simp [supNorm_zero]⟩
    · rw [mem_singleton.1 h2]
      exact ⟨y, mem_blockSet_blk j y, z, mem_blockSet_blk j z, by rwa [supNorm_sub_comm]⟩
    · rw [mem_singleton.1 h1]
      exact ⟨z, mem_blockSet_blk j z, y, mem_blockSet_blk j y, hz⟩
    · rw [mem_singleton.1 h1, mem_singleton.1 h2]
      exact ⟨z, mem_blockSet_blk j z, z, mem_blockSet_blk j z, by simp [supNorm_zero]⟩
  have hsmall : IsSmall j S := by
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
  exact ⟨S, hsmall, hzS, blk j y, blk_mem_blocks hy, subset_union_left⟩

/-- `nbhd` is monotone in `X` -/
theorem nbhd_mono {j : ℕ} {X Y : Finset (Lam d L N)} (h : Y ⊆ X) : nbhd j Y ⊆ nbhd j X := by
  intro w hw
  simp only [nbhd, mem_filter, mem_univ, true_and] at hw ⊢
  obtain ⟨S, hS, hwS, b, hb, hbS⟩ := hw
  exact ⟨S, hS, hwS, b, image_subset_image h hb, hbS⟩

end

end Loc
