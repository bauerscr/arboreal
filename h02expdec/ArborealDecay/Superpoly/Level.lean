module

public import ArborealDecay.Surgery
public import ArborealDecay.ExpDecay.Defs
public import ArborealDecay.Superpoly.Restrict

/-!
# Wiring a level set

The wiring input `(W)` is formulated on the quotient type `Option {v // v ∉ S}`.  Here it is
transported to a *same-type* collapse of a level set `{h = t}` of a height function `h` to one
of its points `ρ`, so that successive wirings stay on one type and compose.
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay

/-- The support graph `u ~ v ↔ u ≠ v ∧ β u v ≠ 0`. -/
def suppGraph {V : Type*} (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) : SimpleGraph V where
  Adj u v := u ≠ v ∧ β u v ≠ 0
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [hβ]; exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

theorem suppGraph_adj {V : Type*} (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (u v : V) :
    (suppGraph β hβ).Adj u v ↔ u ≠ v ∧ β u v ≠ 0 := Iff.rfl

/-- Collapsing a vertex set `S` to one point (`none`). -/
def collapse {V : Type*} [DecidableEq V] (S : Finset V) (v : V) : Option {v // v ∉ S} :=
  if h : v ∈ S then none else some ⟨v, h⟩

theorem arborealProb_reach_comm {V : Type*} [Fintype V] [DecidableEq V] (β : V → V → ℝ)
    (hβ : ∀ i j, β i j = β j i) (x y : V) :
    H02.arborealProb β hβ (fun F => F.Reachable x y) =
      H02.arborealProb β hβ (fun F => F.Reachable y x) := by
  unfold H02.arborealProb
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext F
  simp only [mem_filter, mem_univ, true_and, SimpleGraph.reachable_comm (u := x) (v := y)]

section

variable {T : Type} [Fintype T] [DecidableEq T]

/-- Collapse the level set `{h = t}` to the point `ρ`. -/
def lvlCollapse (h : T → ℤ) (t : ℤ) (ρ : T) (v : T) : T := if h v = t then ρ else v

theorem h_lvlCollapse {h : T → ℤ} {t : ℤ} {ρ : T} (hρ : h ρ = t) (v : T) :
    h (lvlCollapse h t ρ v) = h v := by
  unfold lvlCollapse; split_ifs with hv
  · rw [hρ, hv]
  · rfl

theorem mapW_lip {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
    {β : Λ → Λ → ℝ} (f : Λ → Λ') (h : Λ → ℤ) (h' : Λ' → ℤ) (hf : ∀ u, h' (f u) = h u)
    (hLip : ∀ u v, β u v ≠ 0 → |h u - h v| ≤ 1) (a b : Λ') (hab : mapW β f a b ≠ 0) :
    |h' a - h' b| ≤ 1 := by
  unfold mapW at hab
  by_cases hab' : a = b
  · simp [hab'] at hab
  · simp only [hab', ite_false] at hab
    obtain ⟨u, hu, hu'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
    obtain ⟨v, hv, hv'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu'
    simp only [mem_filter, mem_univ, true_and] at hu hv
    have := hLip u v hv'
    rw [← hu, ← hv, hf, hf]
    exact this

theorem mapW_diag {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
    (β : Λ → Λ → ℝ) (f : Λ → Λ') (a : Λ') : mapW β f a a = 0 := by
  unfold mapW; simp

/-- **One wiring step** (from `(W)`): wiring the level set `{h = t}` separating `a` from `b`
can only increase `μ(a ↔ b)`; the wired graph lives on the same type. -/
theorem wireLevel_of_inputs
    (hW : ∀ (V : Type) [Fintype V] [DecidableEq V] (β : V → V → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) →
      ∀ (S : Finset V) (a b : V), a ∉ S → b ∉ S →
        (∀ p : (suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ S) →
        connProb β hβ a b ≤
          connProb (mapW β (collapse S)) (mapW_symm hβ _) (collapse S a) (collapse S b))
    (h : T → ℤ) (t : ℤ) (ρ : T) (hρ : h ρ = t) {β : T → T → ℝ} (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) (hLip : ∀ u v, β u v ≠ 0 → |h u - h v| ≤ 1) {a b : T}
    (ha : h a < t) (hb : t < h b) :
    connProb β hβ a b ≤ connProb (mapW β (lvlCollapse h t ρ)) (mapW_symm hβ _) a b := by
  set S : Finset T := univ.filter (fun v => h v = t) with hS
  have haS : a ∉ S := by simp [hS]; omega
  have hbS : b ∉ S := by simp [hS]; omega
  have hsep : ∀ p : (suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ S := by
    intro p
    obtain ⟨v, hv, hvt⟩ := Lattice.exists_mem_support_eq_of_lipschitz (G := suppGraph β hβ) h
      (fun x y hxy => hLip x y ((suppGraph_adj β hβ x y).1 hxy).2) p (r := t) ha.le hb.le
    exact ⟨v, hv, by simp [hS, hvt]⟩
  have h1 := hW T β hβ hβ0 S a b haS hbS hsep
  set q : T → Option {v // v ∉ S} := collapse S with hq
  let j : Option {v // v ∉ S} → T := fun o => o.elim ρ Subtype.val
  have hρS : ρ ∈ S := by simp [hS, hρ]
  have hj : Function.Injective j := by
    intro o o' hoo
    cases o with
    | none =>
      cases o' with
      | none => rfl
      | some v =>
        have : (v : T) = ρ := by simpa [j] using hoo.symm
        exact absurd (this ▸ hρS) v.2
    | some v =>
      cases o' with
      | none =>
        have : (v : T) = ρ := by simpa [j] using hoo
        exact absurd (this ▸ hρS) v.2
      | some v' => exact congrArg some (Subtype.ext (by simpa [j] using hoo))
  have hjq : j ∘ q = lvlCollapse h t ρ := by
    funext v
    by_cases hv : v ∈ S
    · have : h v = t := by simpa [hS] using hv
      simp [hq, collapse, hv, j, lvlCollapse, this]
    · have : h v ≠ t := by simpa [hS] using hv
      simp [hq, collapse, hv, j, lvlCollapse, this]
  have hγ := mapW_symm hβ q
  have hβ' : ∀ u v, mapW (mapW β q) j u v = mapW (mapW β q) j v u :=
    mapW_symm hγ j
  have hnn : ∀ u v, 0 ≤ mapW β q u v := mapW_nonneg hβ0 q
  have hcmp := arborealProb_reach_embed j hj hβ' hγ (mapW_nonneg hnn j)
    (fun u v huv => by
      rcases huv with h | h
      · exact mapW_not_range_left _ h v
      · exact mapW_not_range_right _ h u)
    (fun a b => mapW_inj_apply hj (mapW β q) (mapW_diag β q) a b) (q a) (q b)
  have hmw : mapW (mapW β q) j = mapW β (lvlCollapse h t ρ) := by
    funext u v
    rw [mapW_comp, hjq]
  have hqa : j (q a) = a := by
    have := congrFun hjq a
    simp only [Function.comp] at this
    rw [this]; simp [lvlCollapse]; omega
  have hqb : j (q b) = b := by
    have := congrFun hjq b
    simp only [Function.comp] at this
    rw [this]; simp [lvlCollapse]; omega
  refine h1.trans (le_of_eq ?_)
  unfold connProb
  rw [arborealProb_reach_comm _ hγ, ← hcmp]
  simp only [hqa, hqb, hmw]
  exact arborealProb_reach_comm _ _ _ _

end

end

end ArborealDecay.Superpoly
