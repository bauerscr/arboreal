module

public import ArborealDecay.Surgery
public import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Wiring a set `S` together: the collapse map and a star on `S`

* `collapse S : V → Option {v // v ∉ S}` identifies all vertices of `S` to one vertex `none`.
* `starA S s₀` is a star (a tree) on the vertex set `S`, centered at `s₀ ∈ S`; its components are
  the fibres of `collapse S`.
* `SepS S F`: the vertices of `S` lie in pairwise distinct components of `F`.
  For a forest `F`, `starA ⊔ F` is acyclic iff `SepS S F` (`isAcyclic_sup_of_sep`,
  `sepS_sdiff_of_isAcyclic`).
-/

@[expose] public section

namespace ArborealDecay.Wiring

noncomputable section

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Identify all the vertices of `S` to one point (`none`). -/
def collapse (S : Finset V) (v : V) : Option {v // v ∉ S} :=
  if h : v ∈ S then none else some ⟨v, h⟩

theorem collapse_of_mem {S : Finset V} {v : V} (h : v ∈ S) : collapse S v = none := by
  simp [collapse, h]

theorem collapse_of_notMem {S : Finset V} {v : V} (h : v ∉ S) :
    collapse S v = some ⟨v, h⟩ := by
  simp [collapse, h]

/-- A star on `S` centered at `s₀ ∈ S`. -/
def starA (S : Finset V) (s₀ : V) (hs₀ : s₀ ∈ S) : SimpleGraph V :=
  (SimpleGraph.starGraph (⟨s₀, hs₀⟩ : ↥S)).map (Function.Embedding.subtype _)

variable {S : Finset V} {s₀ : V} (hs₀ : s₀ ∈ S)

theorem starA_mem {u v : V} (h : (starA S s₀ hs₀).Adj u v) : u ∈ S ∧ v ∈ S := by
  obtain ⟨x, y, _, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 h
  exact ⟨x.2, y.2⟩

theorem starA_isAcyclic : (starA S s₀ hs₀).IsAcyclic :=
  ArborealDecay.Surgery.isAcyclic_map _ (SimpleGraph.isAcyclic_starGraph _)

theorem starA_reachable {u v : V} (hu : u ∈ S) (hv : v ∈ S) : (starA S s₀ hs₀).Reachable u v :=
  (ArborealDecay.Surgery.reachable_map_iff (Function.Embedding.subtype _)
    (SimpleGraph.starGraph (⟨s₀, hs₀⟩ : ↥S)) ⟨u, hu⟩ ⟨v, hv⟩).2
    ((SimpleGraph.connected_starGraph _).preconnected _ _)

theorem starA_hA : ∀ u v, (starA S s₀ hs₀).Reachable u v ↔ collapse S u = collapse S v := by
  intro u v
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | @tail b c _ hbc ih =>
      obtain ⟨hb, hc⟩ := starA_mem hs₀ hbc
      rw [ih, collapse_of_mem hb, collapse_of_mem hc]
  · intro h
    by_cases hu : u ∈ S
    · have hv : v ∈ S := by
        by_contra hv
        rw [collapse_of_mem hu, collapse_of_notMem hv] at h
        exact absurd h (by simp)
      exact starA_reachable hs₀ hu hv
    · have hv : v ∉ S := by
        intro hv
        rw [collapse_of_notMem hu, collapse_of_mem hv] at h
        exact absurd h (by simp)
      rw [collapse_of_notMem hu, collapse_of_notMem hv] at h
      have := congrArg (fun x => x.map Subtype.val) h
      simp at this
      rw [this]

/-- Reachability in `A ⊔ T`, where `A` only has edges inside `S`. -/
theorem reach_sup_cases {A T : SimpleGraph V} (hA : ∀ u v, A.Adj u v → u ∈ S ∧ v ∈ S) {x y : V}
    (h : (A ⊔ T).Reachable x y) :
    T.Reachable x y ∨ ∃ s ∈ S, ∃ s' ∈ S, T.Reachable x s ∧ T.Reachable s' y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl (SimpleGraph.Reachable.refl _)
  | @tail b c _ hbc ih =>
    rw [SimpleGraph.sup_adj] at hbc
    rcases hbc with hbc | hbc
    · obtain ⟨hb, hc⟩ := hA _ _ hbc
      rcases ih with h1 | ⟨s, hs, s', hs', h1, h2⟩
      · exact Or.inr ⟨b, hb, c, hc, h1, SimpleGraph.Reachable.refl _⟩
      · exact Or.inr ⟨s, hs, c, hc, h1, SimpleGraph.Reachable.refl _⟩
    · rcases ih with h1 | ⟨s, hs, s', hs', h1, h2⟩
      · exact Or.inl (h1.trans hbc.reachable)
      · exact Or.inr ⟨s, hs, s', hs', h1, h2.trans hbc.reachable⟩

/-- Separation of `S`: the vertices of `S` lie in pairwise distinct components of `F`. -/
def SepS (S : Finset V) (F : SimpleGraph V) : Prop :=
  ∀ s ∈ S, ∀ s' ∈ S, F.Reachable s s' → s = s'

theorem SepS.anti {F G : SimpleGraph V} (h : F ≤ G) (hG : SepS S G) : SepS S F :=
  fun s hs s' hs' hr => hG s hs s' hs' (hr.mono h)

theorem SepS.disjoint_star {F : SimpleGraph V} (hF : SepS S F) :
    Disjoint (starA S s₀ hs₀) F := by
  rw [_root_.disjoint_iff]
  ext u v
  simp only [SimpleGraph.inf_adj, SimpleGraph.bot_adj, iff_false, not_and]
  intro h1 h2
  obtain ⟨hu, hv⟩ := starA_mem hs₀ h1
  exact h2.ne (hF u hu v hv h2.reachable)

/-- If `F` is a forest in which the vertices of `S` are separated, then `starA ⊔ F` is a forest. -/
theorem isAcyclic_sup_of_sep {F : SimpleGraph V} (hF : F.IsAcyclic) (hsep : SepS S F) :
    (starA S s₀ hs₀ ⊔ F).IsAcyclic := by
  have hAS := fun u v h => starA_mem hs₀ (u := u) (v := v) h
  have key : ∀ T : Finset (Sym2 V), T ⊆ F.edgeFinset →
      (starA S s₀ hs₀ ⊔ SimpleGraph.fromEdgeSet (↑T : Set (Sym2 V))).IsAcyclic := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      have : starA S s₀ hs₀ ⊔ SimpleGraph.fromEdgeSet (↑(∅ : Finset (Sym2 V)) : Set (Sym2 V)) =
          starA S s₀ hs₀ := by
        ext a b; simp
      rw [this]; exact starA_isAcyclic hs₀
    | @insert e T he ih =>
      intro hT
      have hTF : T ⊆ F.edgeFinset := fun x hx => hT (Finset.mem_insert_of_mem hx)
      have heF : e ∈ F.edgeFinset := hT (Finset.mem_insert_self _ _)
      induction e using Sym2.ind with
      | h u v =>
      have hadj : F.Adj u v := by simpa using heF
      have huv : u ≠ v := hadj.ne
      have hbridge := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hF) hadj
      rw [SimpleGraph.isBridge_iff] at hbridge
      set F1 : SimpleGraph V := SimpleGraph.fromEdgeSet (↑T : Set (Sym2 V)) with hF1
      have hF1le : F1 ≤ F.deleteEdges {s(u, v)} := by
        intro x y hxy
        rw [hF1, SimpleGraph.fromEdgeSet_adj] at hxy
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨?_, ?_⟩
        · simpa using hTF hxy.1
        · intro hmem
          rw [Set.mem_singleton_iff] at hmem
          rw [hmem] at hxy
          exact he (by simpa using hxy.1)
      have hF1F : F1 ≤ F := hF1le.trans (SimpleGraph.deleteEdges_le _)
      have hnr : ¬ (starA S s₀ hs₀ ⊔ F1).Reachable u v := by
        intro hr
        rcases reach_sup_cases hAS hr with h1 | ⟨s, hs, s', hs', h1, h2⟩
        · exact hbridge (h1.mono hF1le)
        · have hss' : F.Reachable s s' := (h1.mono hF1F).symm.trans
            (hadj.reachable.trans (h2.mono hF1F).symm)
          have := hsep s hs s' hs' hss'
          subst this
          exact hbridge ((h1.trans h2).mono hF1le)
      have hna : ¬ (starA S s₀ hs₀ ⊔ F1).Adj u v := fun h => hnr h.reachable
      have hins : starA S s₀ hs₀ ⊔ SimpleGraph.fromEdgeSet (↑(insert s(u, v) T) : Set (Sym2 V)) =
          (starA S s₀ hs₀ ⊔ F1) ⊔ SimpleGraph.edge u v :=
        ArborealDecay.Surgery.edge_graph_insert T u v
      rw [hins, H02.acyclic_sup_edge_iff huv hna]
      exact ⟨ih hTF, hnr⟩
  have := key F.edgeFinset (Finset.Subset.refl _)
  rwa [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet] at this

/-- If `starA ≤ F` and `F` is a forest, the vertices of `S` are separated in `F \ starA`. -/
theorem sepS_sdiff_of_isAcyclic {F : SimpleGraph V} (hF : F.IsAcyclic) (hAF : starA S s₀ hs₀ ≤ F) :
    SepS S (F \ starA S s₀ hs₀) := by
  intro s hs s' hs' hr
  by_contra hne
  obtain ⟨p, hp⟩ := hr.exists_isPath
  obtain ⟨q, hq⟩ := (starA_reachable hs₀ hs hs').exists_isPath
  have hle : F \ starA S s₀ hs₀ ≤ F := sdiff_le
  have h1 := SimpleGraph.isAcyclic_iff_path_unique.1 hF ⟨p.mapLe hle, hp.mapLe hle⟩
    ⟨q.mapLe hAF, hq.mapLe hAF⟩
  have h2 : p.mapLe hle = q.mapLe hAF := congrArg Subtype.val h1
  have hpn : p.edges ≠ [] := by
    intro h
    cases p with
    | nil => exact hne rfl
    | cons h' p' => simp at h
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hpn
  have he2 : e ∈ q.edges := by
    have := congrArg SimpleGraph.Walk.edges h2
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges, SimpleGraph.Walk.edges_mapLe_eq_edges] at this
    rw [← this]; exact he
  have hA := q.edges_subset_edgeSet he2
  have hB := p.edges_subset_edgeSet he
  induction e using Sym2.ind with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet] at hA hB
    exact hB.2 hA

end

end ArborealDecay.Wiring
