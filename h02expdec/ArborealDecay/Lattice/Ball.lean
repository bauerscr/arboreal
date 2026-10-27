module

public import Mathlib
public import ArborealDecay.Lattice.Basic

/-!
# Boxes and shells in `ℤ²`, shell counting and the exit-edge count
-/

@[expose] public section

namespace ArborealDecay.Lattice

/-- The closed square `{z | supDist y z ≤ R}` as a finset. -/
def ball (y : ℤ × ℤ) (R : ℤ) : Finset (ℤ × ℤ) :=
  Finset.Icc (y.1 - R) (y.1 + R) ×ˢ Finset.Icc (y.2 - R) (y.2 + R)

/-- The shell `{z | supDist y z = k}` as a finset. -/
def shell (y : ℤ × ℤ) (k : ℤ) : Finset (ℤ × ℤ) := ball y k \ ball y (k - 1)

theorem supDist_le_iff_left {y z : ℤ × ℤ} {R : ℤ} :
    supDist y z ≤ R ↔ z.1 - R ≤ y.1 ∧ y.1 ≤ z.1 + R ∧ z.2 - R ≤ y.2 ∧ y.2 ≤ z.2 + R := by
  rw [supDist_comm, supDist_le_iff']; omega

theorem supDist_eq_iff {y z : ℤ × ℤ} {k : ℤ} :
    supDist y z = k ↔ supDist y z ≤ k ∧ ¬ supDist y z ≤ k - 1 := by omega

theorem mem_ball {y z : ℤ × ℤ} {R : ℤ} : z ∈ ball y R ↔ supDist y z ≤ R := by
  rw [supDist_comm, supDist_le_iff']
  simp only [ball, Finset.mem_product, Finset.mem_Icc]; omega

theorem mem_shell {y z : ℤ × ℤ} {k : ℤ} : z ∈ shell y k ↔ supDist y z = k := by
  have := supDist_nonneg y z
  simp only [shell, Finset.mem_sdiff, mem_ball]; omega

theorem ball_mono (y : ℤ × ℤ) {R S : ℤ} (h : R ≤ S) : ball y R ⊆ ball y S := by
  intro z; simp only [mem_ball]; omega

theorem card_ball (y : ℤ × ℤ) {R : ℤ} (hR : 0 ≤ R) : ((ball y R).card : ℤ) = (2 * R + 1) ^ 2 := by
  simp only [ball, Finset.card_product, Int.card_Icc]
  push_cast
  rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
  ring

/-- Shell counting: `#{z | supDist y z = k} = 8k` for `k ≥ 1`. -/
theorem card_shell (y : ℤ × ℤ) {k : ℤ} (hk : 1 ≤ k) : ((shell y k).card : ℤ) = 8 * k := by
  have h := Finset.card_sdiff_of_subset (ball_mono y (show k - 1 ≤ k by omega))
  unfold shell
  rw [h]; push_cast [Finset.card_le_card (ball_mono y (show k - 1 ≤ k by omega))]
  rw [card_ball y (by omega), card_ball y (by omega)]; ring

theorem card_shell_zero (y : ℤ × ℤ) : (shell y 0).card = 1 := by
  have : shell y 0 = {y} := by
    ext z
    rw [mem_shell, Finset.mem_singleton]
    constructor
    · intro h; exact (supDist_eq_zero.mp h).symm
    · rintro rfl; exact supDist_self _
  rw [this]; simp

/-- Ordered nearest-neighbour pairs `(u, v)` with `u` in the closed square of radius `R` and
`v` outside it. -/
def exitEdges (y : ℤ × ℤ) (R : ℤ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (ball y R ×ˢ ball y (R + 1)).filter (fun p => R < supDist y p.2 ∧ IsNN p.1 p.2)

theorem mem_exitEdges {y u v : ℤ × ℤ} {R : ℤ} :
    (u, v) ∈ exitEdges y R ↔ supDist y u ≤ R ∧ R < supDist y v ∧ IsNN u v := by
  simp only [exitEdges, Finset.mem_filter, Finset.mem_product, mem_ball]
  constructor
  · rintro ⟨⟨h1, _⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    have a := abs_supDist_sub_le' h3 y
    have b := h3.supDist_le_one
    have := supDist_triangle y u v
    exact ⟨⟨h1, by
      have := supDist_triangle y u v
      have := h3.supDist_le_one
      omega⟩, h2, h3⟩

theorem exitEdges_supDist {y u v : ℤ × ℤ} {R : ℤ} (h : (u, v) ∈ exitEdges y R) :
    supDist y u = R ∧ supDist y v = R + 1 := by
  rw [mem_exitEdges] at h
  obtain ⟨h1, h2, h3⟩ := h
  have := supDist_triangle y u v
  have := h3.supDist_eq_one
  have := supDist_triangle y v u
  have := h3.symm.supDist_eq_one
  constructor <;> omega

/-- The four corners of the square of radius `R + 1` around `y`. -/
def corners (y : ℤ × ℤ) (R : ℤ) : Finset (ℤ × ℤ) :=
  {y + (R + 1, R + 1), y + (R + 1, -(R + 1)), y + (-(R + 1), R + 1), y + (-(R + 1), -(R + 1))}

theorem card_corners (y : ℤ × ℤ) {R : ℤ} (hR : 0 ≤ R) : (corners y R).card = 4 := by
  unfold corners
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · simp only [Finset.mem_singleton, Prod.ext_iff, Prod.fst_add, Prod.snd_add]; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add]; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add]; omega

theorem corners_subset_shell (y : ℤ × ℤ) {R : ℤ} (hR : 0 ≤ R) :
    corners y R ⊆ shell y (R + 1) := by
  intro z hz
  rw [mem_shell, supDist_eq_iff, supDist_le_iff_left, supDist_le_iff_left]
  simp only [corners, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
  · simp only [Prod.fst_add, Prod.snd_add]; omega

/-- Edge count: at most `8R + 4` ordered nearest-neighbour pairs leave the square of radius
`R`. -/
theorem card_exitEdges_le (y : ℤ × ℤ) {R : ℤ} (hR : 0 ≤ R) :
    ((exitEdges y R).card : ℤ) ≤ 8 * R + 4 := by
  have hinj : Set.InjOn (fun p : (ℤ × ℤ) × (ℤ × ℤ) => p.2) (exitEdges y R) := by
    rintro ⟨u, v⟩ hp ⟨u', v'⟩ hq (h : v = v')
    subst h
    rw [Finset.mem_coe, mem_exitEdges] at hp hq
    obtain ⟨hu, hv, hn⟩ := hp
    obtain ⟨hu', _, hn'⟩ := hq
    have e1 := exitEdges_supDist (mem_exitEdges.mpr ⟨hu, hv, hn⟩)
    have e2 := exitEdges_supDist (mem_exitEdges.mpr ⟨hu', hv, hn'⟩)
    have e1' := e1.1
    have e2' := e2.1
    have f1 := e1.2
    clear hu hu' hv
    simp only [supDist_eq_iff, supDist_le_iff_left] at e1' e2' f1 e1 e2
    rw [isNN_iff] at hn hn'
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, and_true] at hn hn' ⊢
    clear e1 e2
    simp only [not_and_or, not_le] at e1' e2' f1
    rcases hn with h | h | h | h <;> rcases hn' with h' | h' | h' | h' <;> omega
  have hmap : ∀ p ∈ exitEdges y R, p.2 ∈ shell y (R + 1) \ corners y R := by
    rintro ⟨u, v⟩ hp
    have e := exitEdges_supDist hp
    rw [mem_exitEdges] at hp
    obtain ⟨hu, hv, hn⟩ := hp
    simp only [Finset.mem_sdiff, mem_shell, corners, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨e.2, ?_⟩
    have e1 := e.1
    have e2 := e.2
    simp only [supDist_eq_iff, supDist_le_iff_left] at e1 e2
    rw [supDist_le_iff_left] at hu
    rw [isNN_iff] at hn
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hn ⊢
    omega
  have := Finset.card_le_card_of_injOn _ hmap hinj
  rw [Finset.card_sdiff_of_subset (corners_subset_shell y hR), card_corners y hR] at this
  have h8 := card_shell y (show 1 ≤ R + 1 by omega)
  have : (4 : ℕ) ≤ (shell y (R + 1)).card := by
    have := Finset.card_le_card (corners_subset_shell y hR)
    rwa [card_corners y hR] at this
  omega

end ArborealDecay.Lattice
