import Step.Defs

/-!
# Auxiliary combinatorics for `Step.Polymers`

Abstract facts about block index vectors `Fin d → ℕ`:

* relations restricted to finite sets and connectedness (`restr`, `Conn`);
* cyclic adjacency of block indices (`cyc`, `Adj`), neighbourhoods and balls (`Nbr`, `Ball`);
* the cluster lemma: a connected set of `j`-blocks lying in pairwise distinct `(j+1)`-blocks
  has at most `2^d` elements, for `L > 2^d` (`cluster`).
-/

namespace Step.PolyAux

open Finset

open Classical

/-! ### Relations restricted to finite sets -/

section Rel

variable {α : Type*}

/-- The restriction of a relation to a finite set. -/
def restr (C : Finset α) (R : α → α → Prop) (x y : α) : Prop := x ∈ C ∧ y ∈ C ∧ R x y

/-- `C` is connected for `R`. -/
def Conn (R : α → α → Prop) (C : Finset α) : Prop :=
  ∀ z ∈ C, ∀ z' ∈ C, Relation.ReflTransGen (restr C R) z z'

theorem restr_symm {C : Finset α} {R : α → α → Prop} (hR : Symmetric R) :
    Symmetric (restr C R) := fun _ _ h => ⟨h.2.1, h.1, hR h.2.2⟩

theorem rtg_restr_mono {C D : Finset α} {R R' : α → α → Prop} (hCD : C ⊆ D)
    (hRR : ∀ x y, R x y → R' x y) {a b : α} (h : Relation.ReflTransGen (restr C R) a b) :
    Relation.ReflTransGen (restr D R') a b :=
  h.mono fun x y hxy => ⟨hCD hxy.1, hCD hxy.2.1, hRR _ _ hxy.2.2⟩

theorem mem_of_rtg_restr {C : Finset α} {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen (restr C R) a b) (ha : a ∈ C) : b ∈ C := by
  induction h with
  | refl => exact ha
  | tail _ hce _ => exact hce.2.1

/-- The reachable set from `u` inside `C` is connected. -/
theorem conn_filter_reach {R : α → α → Prop} (hR : Symmetric R) {C : Finset α} {u : α}
    (hu : u ∈ C) : Conn R (C.filter (Relation.ReflTransGen (restr C R) u)) := by
  set K := C.filter (Relation.ReflTransGen (restr C R) u) with hK
  have key : ∀ z, Relation.ReflTransGen (restr C R) u z → Relation.ReflTransGen (restr K R) u z := by
    intro z hz
    induction hz with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c e hc hce ih =>
      refine ih.tail ⟨?_, ?_, hce.2.2⟩
      · exact mem_filter.2 ⟨hce.1, hc⟩
      · exact mem_filter.2 ⟨hce.2.1, hc.tail hce⟩
  intro z hz z' hz'
  have h1 := key z (mem_filter.1 hz).2
  have h2 := key z' (mem_filter.1 hz').2
  exact (Relation.ReflTransGen.symmetric (restr_symm hR) h1).trans h2

theorem exists_exit {R : α → α → Prop} {P : α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) (ha : P a) (hb : ¬ P b) : ∃ u, P u ∧ ∃ v, ¬ P v ∧ R u v := by
  revert hb
  induction h with
  | refl => intro hb; exact absurd ha hb
  | @tail c e _ hce ih =>
    intro hb
    by_cases hc : P c
    · exact ⟨c, hc, e, hb, hce⟩
    · exact ih hc

/-- Discrete intermediate value theorem along a path. -/
theorem ivt {R : α → α → Prop} (f : α → ℕ) (hf : ∀ x y, R x y → f y ≤ f x + 1)
    {a b : α} (h : Relation.ReflTransGen R a b) :
    ∀ w, f a ≤ w → w ≤ f b → ∃ z, Relation.ReflTransGen R a z ∧ f z = w := by
  induction h with
  | refl => intro w h1 h2; exact ⟨a, Relation.ReflTransGen.refl, by omega⟩
  | @tail c e hc hce ih =>
    intro w h1 h2
    by_cases hw : w ≤ f c
    · exact ih w h1 hw
    · have := hf _ _ hce
      exact ⟨e, hc.tail hce, by omega⟩

end Rel

/-! ### Cyclic adjacency -/

/-- `a` and `a'` are at cyclic distance `≤ 1` in `ℤ/Mℤ`. -/
def cyc (M a a' : ℕ) : Prop :=
  a' = a ∨ a' = a + 1 ∨ a = a' + 1 ∨ (a = 0 ∧ a' = M - 1) ∨ (a' = 0 ∧ a = M - 1)

/-- Adjacency of block indices. -/
def Adj {d : ℕ} (M : ℕ) (u v : Fin d → ℕ) : Prop := ∀ i, cyc M (u i) (v i)

theorem cyc_symm {M a a' : ℕ} (h : cyc M a a') : cyc M a' a := by
  unfold cyc at *; omega

theorem adj_symm {d M : ℕ} : Symmetric (Adj (d := d) M) := fun _ _ h i => cyc_symm (h i)

theorem adj_refl {d M : ℕ} (u : Fin d → ℕ) : Adj M u u := fun _ => Or.inl rfl

/-- The parent (next scale block) of a block index. -/
def par {d : ℕ} (L : ℕ) (b : Fin d → ℕ) : Fin d → ℕ := fun i => b i / L

theorem div_mod_of_eq {L q r a : ℕ} (hL : 0 < L) (hr : r < L) (h : a = L * q + r) :
    a / L = q ∧ a % L = r := by
  rw [Nat.div_mod_unique hL]; exact ⟨by rw [h]; ring, hr⟩

theorem decomp (L a : ℕ) : a = L * (a / L) + a % L := (Nat.div_add_mod a L).symm

theorem pred_div_mod {L M' : ℕ} (hL : 0 < L) (hM : 0 < M') :
    (L * M' - 1) / L = M' - 1 ∧ (L * M' - 1) % L = L - 1 := by
  apply div_mod_of_eq hL (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, M' = k + 1 := ⟨M' - 1, by omega⟩
  simp only [Nat.add_sub_cancel, mul_add, mul_one]
  omega

/-- same parent: the offsets differ by at most one -/
theorem cyc_same_par {L M' a a' : ℕ} (hL : 0 < L) (hM : 2 ≤ M') (h : cyc (L * M') a a')
    (hp : a / L = a' / L) : a' % L ≤ a % L + 1 := by
  have ea := decomp L a
  have ea' := decomp L a'
  rw [hp] at ea
  rcases h with h | h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h; omega
  · omega
  · omega
  · exfalso
    have := (pred_div_mod hL (by omega : 0 < M')).1
    rw [← h2, ← hp, h1, Nat.zero_div] at this
    omega
  · subst h1; simp

/-- `p ↦ p + 1` in `ℤ/M'ℤ`. -/
def up (M' p : ℕ) : ℕ := if p + 1 = M' then 0 else p + 1

/-- `p ↦ p - 1` in `ℤ/M'ℤ`. -/
def down (M' p : ℕ) : ℕ := if p = 0 then M' - 1 else p - 1

theorem up_down {M' p : ℕ} (hp : p < M') : up M' (down M' p) = p := by
  by_cases h : p = 0
  · subst h; simp only [down, if_true, up]; rw [if_pos (by omega)]
  · simp only [down, h, if_false, up]; rw [if_neg (by omega)]; omega

theorem down_up {M' p : ℕ} (hp : p < M') : down M' (up M' p) = p := by
  by_cases h : p + 1 = M'
  · simp only [up, h, if_true, down]; omega
  · simp only [up, h, if_false, down]; rw [if_neg (by omega)]; omega

/-- different parents: crossing a boundary of the next scale -/
theorem cyc_diff_par {L M' a a' : ℕ} (hL : 0 < L) (ha : a < L * M') (ha' : a' < L * M')
    (h : cyc (L * M') a a') (hp : a / L ≠ a' / L) :
    (a % L = L - 1 ∧ a' % L = 0 ∧ a' / L = up M' (a / L)) ∨
    (a % L = 0 ∧ a' % L = L - 1 ∧ a' / L = down M' (a / L)) := by
  have hM : 0 < M' := by
    rcases Nat.eq_zero_or_pos M' with h0 | h0
    · subst h0; simp at ha
    · exact h0
  have ea := decomp L a
  have ea' := decomp L a'
  have hra := Nat.mod_lt a hL
  have hra' := Nat.mod_lt a' hL
  rcases h with h | h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h; exact absurd rfl hp
  · -- a' = a + 1
    by_cases hr : a % L + 1 < L
    · exfalso
      exact hp (div_mod_of_eq (a := a') (q := a / L) (r := a % L + 1) hL hr (by omega)).1.symm
    · have e : a' = L * (a / L + 1) + 0 := by rw [mul_add, mul_one]; omega
      have hq := div_mod_of_eq hL hL e
      refine Or.inl ⟨by omega, hq.2, ?_⟩
      rw [hq.1]
      unfold up
      split_ifs with hh
      · exfalso; rw [hh] at e; omega
      · rfl
  · -- a = a' + 1
    by_cases hr : a' % L + 1 < L
    · exfalso
      exact hp (div_mod_of_eq (a := a) (q := a' / L) (r := a' % L + 1) hL hr (by omega)).1
    · have e : a = L * (a' / L + 1) + 0 := by rw [mul_add, mul_one]; omega
      have hq := div_mod_of_eq hL hL e
      refine Or.inr ⟨hq.2, by omega, ?_⟩
      rw [hq.1]
      unfold down
      simp
  · have := pred_div_mod hL hM
    rw [← h2] at this
    subst h1
    refine Or.inr ⟨by simp, this.2, ?_⟩
    rw [this.1]; simp [down]
  · have := pred_div_mod hL hM
    rw [← h2] at this
    subst h1
    refine Or.inl ⟨this.2, by simp, ?_⟩
    rw [this.1]; simp only [Nat.zero_div, up]
    rw [if_pos (by omega)]

/-! ### Neighbourhoods and balls -/

/-- The candidate values of a coordinate adjacent to `a`. -/
def nbrVal (M a : ℕ) : Fin 5 → ℕ := ![a, a + 1, a - 1, M - 1, 0]

/-- A finite set containing all indices adjacent to `b`. -/
def Nbr {d : ℕ} (M : ℕ) (b : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  (univ : Finset (Fin d → Fin 5)).image fun δ i => nbrVal M (b i) (δ i)

theorem mem_Nbr {d M : ℕ} {b b' : Fin d → ℕ} (h : Adj M b b') : b' ∈ Nbr M b := by
  have : ∀ i, ∃ k : Fin 5, nbrVal M (b i) k = b' i := by
    intro i
    rcases h i with h | h | h | ⟨_, h⟩ | ⟨h, _⟩
    · exact ⟨0, by simp [nbrVal, h]⟩
    · exact ⟨1, by simp [nbrVal, h]⟩
    · exact ⟨2, by simp [nbrVal]; omega⟩
    · exact ⟨3, by simp [nbrVal, h]⟩
    · exact ⟨4, by simp [nbrVal, h]⟩
  choose δ hδ using this
  exact mem_image.2 ⟨δ, mem_univ _, funext hδ⟩

theorem card_Nbr {d M : ℕ} (b : Fin d → ℕ) : (Nbr M b).card ≤ 5 ^ d := by
  refine card_image_le.trans ?_
  simp

/-- The ball of radius `k` around `b` for the adjacency. -/
def Ball {d : ℕ} (M : ℕ) (b : Fin d → ℕ) : ℕ → Finset (Fin d → ℕ)
  | 0 => {b}
  | k + 1 => (Ball M b k).biUnion (Nbr M)

theorem Ball_zero {d M : ℕ} (b : Fin d → ℕ) : Ball M b 0 = {b} := rfl

theorem Ball_succ {d M : ℕ} (b : Fin d → ℕ) (k : ℕ) :
    Ball M b (k + 1) = (Ball M b k).biUnion (Nbr M) := rfl

theorem Ball_succ_sub {d M : ℕ} (b : Fin d → ℕ) (k : ℕ) : Ball M b k ⊆ Ball M b (k + 1) := by
  intro z hz
  rw [Ball_succ]
  exact mem_biUnion.2 ⟨z, hz, mem_Nbr (adj_refl z)⟩

theorem Ball_mono {d M : ℕ} (b : Fin d → ℕ) {k k' : ℕ} (h : k ≤ k') :
    Ball M b k ⊆ Ball M b k' := by
  induction h with
  | refl => exact subset_refl _
  | step _ ih => exact ih.trans (Ball_succ_sub b _)

theorem card_Ball {d M : ℕ} (b : Fin d → ℕ) (k : ℕ) : (Ball M b k).card ≤ 5 ^ (d * k) := by
  induction k with
  | zero => simp [Ball_zero]
  | succ k ih =>
    rw [Ball_succ]
    refine card_biUnion_le.trans ?_
    calc ∑ z ∈ Ball M b k, (Nbr M z).card ≤ ∑ _z ∈ Ball M b k, 5 ^ d :=
          sum_le_sum fun z _ => card_Nbr z
      _ = (Ball M b k).card * 5 ^ d := by simp
      _ ≤ 5 ^ (d * k) * 5 ^ d := Nat.mul_le_mul_right _ ih
      _ = 5 ^ (d * (k + 1)) := by rw [← pow_add, mul_add, mul_one]

/-- A connected set lies in the ball of radius its cardinality around any of its points. -/
theorem subset_Ball {d M : ℕ} {K : Finset (Fin d → ℕ)} (hK : Conn (Adj M) K) {b : Fin d → ℕ}
    (hb : b ∈ K) : K ⊆ Ball M b K.card := by
  set D : ℕ → Finset (Fin d → ℕ) := fun k => K.filter (· ∈ Ball M b k) with hD
  have hDK : ∀ k, D k ⊆ K := fun k => filter_subset _ _
  have hDm : ∀ k, D k ⊆ D (k + 1) := fun k z hz =>
    mem_filter.2 ⟨(mem_filter.1 hz).1, Ball_succ_sub b k (mem_filter.1 hz).2⟩
  have claim : ∀ k, D k = K ∨ k + 1 ≤ (D k).card := by
    intro k
    induction k with
    | zero =>
      right
      have : b ∈ D 0 := mem_filter.2 ⟨hb, by simp [Ball_zero]⟩
      exact card_pos.2 ⟨b, this⟩
    | succ k ih =>
      by_cases hk : D k = K
      · left
        exact subset_antisymm (hDK _) (fun z hz => hDm k (by rw [hk]; exact hz))
      · right
        rcases ih with ih | ih
        · exact absurd ih hk
        have hss : D k ⊂ D (k + 1) := by
          refine ssubset_of_subset_of_ne (hDm k) ?_
          intro hE
          apply hk
          refine subset_antisymm (hDK _) ?_
          intro z hz
          have hr := hK b hb z hz
          clear hz
          induction hr with
          | refl => exact mem_filter.2 ⟨hb, Ball_mono b (Nat.zero_le k) (by simp [Ball_zero])⟩
          | @tail c e _ hce ih' =>
            rw [hE]
            refine mem_filter.2 ⟨hce.2.1, ?_⟩
            rw [Ball_succ]
            exact mem_biUnion.2 ⟨c, (mem_filter.1 ih').2, mem_Nbr hce.2.2⟩
        have := card_lt_card hss
        omega
  rcases claim K.card with h | h
  · intro z hz
    rw [← h] at hz
    exact (mem_filter.1 hz).2
  · have := card_le_card (hDK K.card)
    omega

/-! ### The cluster lemma -/

section Cluster

variable {d L M' : ℕ}

theorem card_le_of_coord (C : Finset (Fin d → ℕ)) (hinj : Set.InjOn (par (d := d) L) (C : Set (Fin d → ℕ)))
    (h : ∀ i, (C.image fun b => b i / L).card ≤ 2) : C.card ≤ 2 ^ d := by
  rw [← card_image_of_injOn hinj]
  have hsub : C.image (par L) ⊆ Fintype.piFinset fun i => C.image fun b => b i / L := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hp
    exact Fintype.mem_piFinset.2 fun i => mem_image.2 ⟨b, hb, rfl⟩
  refine (card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  calc ∏ i, (C.image fun b => b i / L).card ≤ ∏ _i : Fin d, 2 :=
        prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => h i
    _ = 2 ^ d := by simp

/-- In one coordinate, a connected set with distinct parents takes at most two parent values,
provided that connected subsets in a slab have fewer than `L` elements. -/
theorem coord_two (hL : 2 ≤ L) (C : Finset (Fin d → ℕ)) (i : Fin d)
    (hC : ∀ b ∈ C, ∀ i, b i < L * M')
    (hslab : ∀ K ⊆ C, (∀ b ∈ K, ∀ b' ∈ K, b i / L = b' i / L) → Conn (Adj (L * M')) K →
      K.card < L)
    (hconn : Conn (Adj (L * M')) C) : (C.image fun b => b i / L).card ≤ 2 := by
  have hL0 : 0 < L := by omega
  have hlt : ∀ b ∈ C, b i / L < M' := fun b hb =>
    (Nat.div_lt_iff_lt_mul hL0).2 (by rw [mul_comm]; exact hC b hb i)
  by_cases hM : M' ≤ 2
  · refine (card_le_card (t := range M') ?_).trans (by simpa using hM)
    intro p hp
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hp
    exact mem_range.2 (hlt b hb)
  rw [not_le] at hM
  rcases C.eq_empty_or_nonempty with hCe | ⟨b0, hb0⟩
  · simp [hCe]
  set A := Adj (d := d) (L * M')
  let slab : (Fin d → ℕ) → Finset (Fin d → ℕ) := fun b => C.filter fun b' => b' i / L = b i / L
  let comp : (Fin d → ℕ) → Finset (Fin d → ℕ) := fun b =>
    (slab b).filter (Relation.ReflTransGen (restr (slab b) A) b)
  let Hi : (Fin d → ℕ) → Prop := fun b => ∃ z ∈ comp b, z i % L = L - 1
  let Lo : (Fin d → ℕ) → Prop := fun b => ∃ z ∈ comp b, z i % L = 0
  have mem_comp : ∀ b ∈ C, b ∈ comp b := fun b hb =>
    mem_filter.2 ⟨mem_filter.2 ⟨hb, rfl⟩, Relation.ReflTransGen.refl⟩
  -- (a) a component cannot meet both faces
  have hnot : ∀ b ∈ C, Hi b → Lo b → False := by
    rintro b hb ⟨z1, hz1, e1⟩ ⟨z0, hz0, e0⟩
    have hbs : b ∈ slab b := mem_filter.2 ⟨hb, rfl⟩
    have hconnK := conn_filter_reach (R := A) (C := slab b) adj_symm hbs
    have hsubC : comp b ⊆ C := fun z hz => (mem_filter.1 (mem_filter.1 hz).1).1
    have hcard := hslab (comp b) hsubC (fun x hx y hy => by
      rw [(mem_filter.1 (mem_filter.1 hx).1).2, (mem_filter.1 (mem_filter.1 hy).1).2]) hconnK
    have hpath := hconnK z0 hz0 z1 hz1
    have hsteps : ∀ x y, restr (comp b) A x y → y i % L ≤ x i % L + 1 := by
      intro x y hxy
      have hx := mem_filter.1 (mem_filter.1 hxy.1).1
      have hy := mem_filter.1 (mem_filter.1 hxy.2.1).1
      exact cyc_same_par hL0 (by omega) (hxy.2.2 i) (by rw [hx.2, hy.2])
    have hrange : range L ⊆ (comp b).image fun z => z i % L := by
      intro w hw
      obtain ⟨z, hz, hzw⟩ := ivt (fun z => z i % L) hsteps hpath w
        (by show z0 i % L ≤ w; rw [e0]; exact Nat.zero_le _)
        (by show w ≤ z1 i % L; rw [e1]; have := mem_range.1 hw; omega)
      exact mem_image.2 ⟨z, mem_of_rtg_restr hz hz0, hzw⟩
    have := (card_le_card hrange).trans card_image_le
    rw [card_range] at this
    omega
  -- (c) same parent: same component
  have hsame : ∀ b b', restr C A b b' → b' i / L = b i / L → comp b' = comp b := by
    intro b b' hbb' hp
    have hsl : slab b' = slab b := by
      ext z; simp only [slab, mem_filter, hp]
    have hb's : b' ∈ slab b := mem_filter.2 ⟨hbb'.2.1, hp⟩
    have hbs : b ∈ slab b := mem_filter.2 ⟨hbb'.1, rfl⟩
    have h1 : Relation.ReflTransGen (restr (slab b) A) b b' :=
      Relation.ReflTransGen.single ⟨hbs, hb's, hbb'.2.2⟩
    have h2 := Relation.ReflTransGen.symmetric (restr_symm adj_symm) h1
    simp only [comp, hsl]
    ext z
    simp only [mem_filter]
    constructor
    · rintro ⟨hz, hr⟩; exact ⟨hz, h1.trans hr⟩
    · rintro ⟨hz, hr⟩; exact ⟨hz, h2.trans hr⟩
  -- (d) different parents
  have hdiff : ∀ b b', restr C A b b' → b' i / L ≠ b i / L →
      (Hi b ∧ Lo b' ∧ b' i / L = up M' (b i / L)) ∨
      (Lo b ∧ Hi b' ∧ b' i / L = down M' (b i / L)) := by
    intro b b' hbb' hp
    rcases cyc_diff_par hL0 (hC b hbb'.1 i) (hC b' hbb'.2.1 i) (hbb'.2.2 i) (Ne.symm hp) with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨⟨b, mem_comp b hbb'.1, h1⟩, ⟨b', mem_comp b' hbb'.2.1, h2⟩, h3⟩
    · exact Or.inr ⟨⟨b, mem_comp b hbb'.1, h1⟩, ⟨b', mem_comp b' hbb'.2.1, h2⟩, h3⟩
  set p0 := b0 i / L
  have hp0 := hlt b0 hb0
  by_cases hH : Hi b0
  · -- values in `{p0, up p0}`
    have inv : ∀ b ∈ C, (b i / L = p0 ∧ ¬ Lo b) ∨ (b i / L = up M' p0 ∧ ¬ Hi b) := by
      intro b hb
      have hr := hconn b0 hb0 b hb
      clear hb
      induction hr with
      | refl => exact Or.inl ⟨rfl, fun h => hnot b0 hb0 hH h⟩
      | @tail x y _ hxy ih =>
        by_cases hp : y i / L = x i / L
        · rw [hp]; simp only [Hi, Lo, hsame x y hxy hp]; exact ih
        · rcases hdiff x y hxy hp with ⟨hx, hy, e⟩ | ⟨hx, hy, e⟩
          · rcases ih with ⟨e', _⟩ | ⟨_, h'⟩
            · exact Or.inr ⟨by rw [e, e'], fun h => hnot y hxy.2.1 h hy⟩
            · exact absurd hx h'
          · rcases ih with ⟨_, h'⟩ | ⟨e', _⟩
            · exact absurd hx h'
            · exact Or.inl ⟨by rw [e, e', down_up hp0], fun h => hnot y hxy.2.1 hy h⟩
    refine (card_le_card (t := {p0, up M' p0}) ?_).trans (card_le_two)
    intro p hp
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hp
    rcases inv b hb with ⟨e, _⟩ | ⟨e, _⟩ <;> simp [e]
  · have inv : ∀ b ∈ C, (b i / L = p0 ∧ ¬ Hi b) ∨ (b i / L = down M' p0 ∧ ¬ Lo b) := by
      intro b hb
      have hr := hconn b0 hb0 b hb
      clear hb
      induction hr with
      | refl => exact Or.inl ⟨rfl, hH⟩
      | @tail x y _ hxy ih =>
        by_cases hp : y i / L = x i / L
        · rw [hp]; simp only [Hi, Lo, hsame x y hxy hp]; exact ih
        · rcases hdiff x y hxy hp with ⟨hx, hy, e⟩ | ⟨hx, hy, e⟩
          · rcases ih with ⟨_, h'⟩ | ⟨e', _⟩
            · exact absurd hx h'
            · exact Or.inl ⟨by rw [e, e', up_down hp0], fun h => hnot y hxy.2.1 h hy⟩
          · rcases ih with ⟨e', _⟩ | ⟨_, h'⟩
            · exact Or.inr ⟨by rw [e, e'], fun h => hnot y hxy.2.1 hy h⟩
            · exact absurd hx h'
    refine (card_le_card (t := {p0, down M' p0}) ?_).trans (card_le_two)
    intro p hp
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hp
    rcases inv b hb with ⟨e, _⟩ | ⟨e, _⟩ <;> simp [e]

theorem cluster_aux (hL : 2 ^ d < L) : ∀ (k : ℕ) (F : Finset (Fin d)) (C : Finset (Fin d → ℕ)),
    (univ \ F).card = k → (∀ b ∈ C, ∀ i, b i < L * M') → Set.InjOn (par (d := d) L) (C : Set (Fin d → ℕ)) →
    (∀ i ∈ F, ∀ b ∈ C, ∀ b' ∈ C, b i / L = b' i / L) → Conn (Adj (L * M')) C →
    C.card ≤ 2 ^ d := by
  have hL2 : 2 ≤ L := by
    have := Nat.one_le_two_pow (n := d); omega
  intro k
  induction k with
  | zero =>
    intro F C hk _ hinj hF _
    refine card_le_of_coord C hinj fun i => ?_
    have hi : i ∈ F := by
      by_contra hi
      have : i ∈ univ \ F := mem_sdiff.2 ⟨mem_univ _, hi⟩
      rw [card_eq_zero.1 hk] at this; simp at this
    refine (card_le_one.2 (fun p hp q hq => ?_)).trans (by norm_num)
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hp
    obtain ⟨b', hb', rfl⟩ := mem_image.1 hq
    exact hF i hi b hb b' hb'
  | succ k ih =>
    intro F C hk hC hinj hF hconn
    refine card_le_of_coord C hinj fun i => ?_
    by_cases hi : i ∈ F
    · refine (card_le_one.2 (fun p hp q hq => ?_)).trans (by norm_num)
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hp
      obtain ⟨b', hb', rfl⟩ := mem_image.1 hq
      exact hF i hi b hb b' hb'
    refine coord_two hL2 C i hC (fun K hKC hKi hKconn => ?_) hconn
    have hk' : (univ \ insert i F).card = k := by
      have : univ \ F = insert i (univ \ insert i F) := by
        ext z; by_cases hz : z = i <;> simp [hz, hi]
      rw [this, card_insert_of_notMem (by simp)] at hk
      omega
    have := ih (insert i F) K hk' (fun b hb => hC b (hKC hb)) (hinj.mono (coe_subset.2 hKC))
      (fun i' hi' b hb b' hb' => by
        rcases mem_insert.1 hi' with rfl | hi'
        · exact hKi b hb b' hb'
        · exact hF i' hi' b (hKC hb) b' (hKC hb')) hKconn
    omega

/-- **Cluster lemma.** For `L > 2^d`, a connected set of block indices with pairwise distinct
parents has at most `2^d` elements. -/
theorem cluster (hL : 2 ^ d < L) (C : Finset (Fin d → ℕ)) (hC : ∀ b ∈ C, ∀ i, b i < L * M')
    (hinj : Set.InjOn (par (d := d) L) (C : Set (Fin d → ℕ))) (hconn : Conn (Adj (L * M')) C) : C.card ≤ 2 ^ d :=
  cluster_aux hL _ ∅ C rfl hC hinj (by simp) hconn

end Cluster

end Step.PolyAux
