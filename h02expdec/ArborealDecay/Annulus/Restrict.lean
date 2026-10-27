module

public import ArborealDecay.Annulus.MapW
public import ArborealDecay.H02

/-!
# Discarding the components not containing the terminals (supplement `rem:conn-hyp`)

For weights `β` on `X` and `a : X`, let `C = compOf β a` be the vertex set of the component of `a`
in the support graph.

* `tau_eq_zero_of_not_reachable`: if `b` is not in the component of `a`, then `μ_β(a ↔ b) = 0`.
* `tau_restrict`: if `b ∈ C`, then `μ_β(a ↔ b) = μ_{β|C}(a ↔ b)` (one-vertex union `C ∪ (Cᶜ + a)`).
* `connected_restrict`: the support of `β|C` is connected.
-/

open Real

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.Annulus

open ArborealDecay.TLaw ArborealDecay.Surgery

variable {X : Type*} [Fintype X] [DecidableEq X]

open Classical in
/-- The vertices of the component of `a` in the support graph of `β`. -/
noncomputable def compOf (β : X → X → ℝ) (a : X) : Finset X :=
  Finset.univ.filter fun x => (supportGraph β).Reachable a x

theorem mem_compOf {β : X → X → ℝ} {a x : X} : x ∈ compOf β a ↔ (supportGraph β).Reachable a x := by
  classical
  simp [compOf]

theorem self_mem_compOf (β : X → X → ℝ) (a : X) : a ∈ compOf β a :=
  mem_compOf.2 (SimpleGraph.Reachable.refl a)

theorem cross_zero {β : X → X → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {a u v : X} (hu : u ∈ compOf β a) (hv : v ∉ compOf β a) : β u v = 0 := by
  by_contra h
  have hpos : 0 < β u v := lt_of_le_of_ne (hβ0 u v) (Ne.symm h)
  have huv : u ≠ v := fun e => hv (e ▸ hu)
  have hadj : (supportGraph β).Adj u v := (supportGraph_adj hβ).2 ⟨huv, hpos⟩
  exact hv (mem_compOf.2 ((mem_compOf.1 hu).trans hadj.reachable))

theorem tau_eq_zero_of_not_reachable {β : X → X → ℝ} (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) {a b : X} (hab : ¬ (supportGraph β).Reachable a b) :
    H02.arborealProb β hβ (fun F => F.Reachable a b) = 0 := by
  unfold H02.arborealProb
  rw [div_eq_zero_iff]
  left
  refine Finset.sum_eq_zero fun F hF => ?_
  have hF' : F.IsAcyclic ∧ F.Reachable a b := by simpa using hF
  by_contra h
  unfold H02.forestWeight at h
  rw [Finset.prod_eq_zero_iff] at h
  push Not at h
  have hle : F ≤ supportGraph β := by
    intro u v huv
    have := h s(u, v) (by simpa using huv)
    simp only [Sym2.lift_mk] at this
    exact (supportGraph_adj hβ).2 ⟨F.ne_of_adj huv, lt_of_le_of_ne (hβ0 u v) (Ne.symm this)⟩
  exact hab (hF'.2.mono hle)

/-- **Restriction to the component of the terminals**: `μ_β(a ↔ b) = μ_{β|C}(a ↔ b)`. -/
theorem tau_restrict {β : X → X → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {a b : X} (hb : b ∈ compOf β a) :
    H02.arborealProb β hβ (fun F => F.Reachable a b) =
      H02.arborealProb (fun u v : compOf β a => β u v) (fun u v => hβ u v)
        (fun F => F.Reachable ⟨a, self_mem_compOf β a⟩ ⟨b, hb⟩) := by
  set C := compOf β a
  have ha : a ∈ C := self_mem_compOf β a
  have hU : OneVertexUnion C (insert a Cᶜ) a :=
    { cover := fun x => by
        by_cases hx : x ∈ C
        · exact Or.inl hx
        · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_compl.2 hx))
      inter := fun x h1 h2 => by
        rcases Finset.mem_insert.1 h2 with h | h
        · exact h
        · exact absurd h1 (Finset.mem_compl.1 h)
      mem₁ := ha
      mem₂ := Finset.mem_insert_self _ _ }
  have hcross : ∀ u v, u ∈ C → u ≠ a → v ∈ insert a Cᶜ → v ≠ a → β u v = 0 := by
    intro u v hu _ hv hva
    rcases Finset.mem_insert.1 hv with h | h
    · exact absurd h hva
    · exact cross_zero hβ hβ0 hu (Finset.mem_compl.1 h)
  have c1 := arborealProb_congr_noCross hβ hcross (fun F => F.Reachable a b)
    (fun F => (resFin C F).Reachable ⟨a, ha⟩ ⟨b, hb⟩ ∧ True) (fun F _ hF => by
      rw [and_true]
      constructor
      · intro h
        exact ((reach_iff_res₁ hU hF hb).1 h.symm).symm
      · intro h
        exact ((reach_iff_res₁ hU hF hb).2 h.symm).symm)
  have e := arborealProb_union hU hβ hcross
    (fun G => G.Reachable ⟨a, ha⟩ ⟨b, hb⟩) (fun _ => True)
  have t2 := H02.arborealProb_true (w := fun u v : (insert a Cᶜ : Finset X) => β u v)
    (fun u v => hβ u v) (fun u v => hβ0 u v)
  rw [c1, e, t2, mul_one]

theorem reachable_restrict {β : X → X → ℝ} (hβ : ∀ i j, β i j = β j i) {a x : X}
    (hx : x ∈ compOf β a) :
    (supportGraph (fun u v : compOf β a => β u v)).Reachable ⟨a, self_mem_compOf β a⟩ ⟨x, hx⟩ := by
  have h := mem_compOf.1 hx
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  suffices H : ∀ y, Relation.ReflTransGen (supportGraph β).Adj a y →
      ∀ hy : y ∈ compOf β a, (supportGraph (fun u v : compOf β a => β u v)).Reachable
        ⟨a, self_mem_compOf β a⟩ ⟨y, hy⟩ from H x h hx
  intro y hy
  induction hy with
  | refl => intro _; exact SimpleGraph.Reachable.refl _
  | @tail c d hac hcd ih =>
    intro hd
    have hc : c ∈ compOf β a := mem_compOf.2 ((SimpleGraph.reachable_iff_reflTransGen _ _).2 hac)
    refine (ih hc).trans (SimpleGraph.Adj.reachable ?_)
    rw [supportGraph_adj (w := fun u v : compOf β a => β u v) (fun u v => hβ u v)]
    rw [supportGraph_adj hβ] at hcd
    exact ⟨fun e => hcd.1 (congrArg Subtype.val e), hcd.2⟩

theorem connected_restrict {β : X → X → ℝ} (hβ : ∀ i j, β i j = β j i) (a : X) :
    (supportGraph (fun u v : compOf β a => β u v)).Connected := by
  have : Nonempty (compOf β a) := ⟨⟨a, self_mem_compOf β a⟩⟩
  refine ⟨fun x y => ?_⟩
  exact (reachable_restrict hβ x.2).symm.trans (reachable_restrict hβ y.2)

end ArborealDecay.Annulus
