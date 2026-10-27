module

public import ArborealDecay.Wiring.Star

/-!
# Forests of `G` with `S` separated are the forests of `G/S`

`sum_sep_eq` is the weight identity of the note's "forest bijection": for every event `Q` on forests
of `Γ = G/S` (vertex set `Option {v // v ∉ S}`, weights `mapW β (collapse S)`),
`∑_{F forest of G, S separated in F, Q (F/S)} w(F) = ∑_{F' forest of Γ, Q F'} w_Γ(F')`.
It is deduced from the contraction identity `contract_sum_event` by adding a star on `S`.
-/

@[expose] public section

namespace ArborealDecay.Wiring

noncomputable section

open Finset Classical ArborealDecay.Surgery

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Finset V} {s₀ : V} (hs₀ : s₀ ∈ S)

/-- The weights `β`, modified to be `1` on the edges of `A`. -/
def betaT (A : SimpleGraph V) (β : V → V → ℝ) (u v : V) : ℝ := if A.Adj u v then 1 else β u v

theorem betaT_symm (A : SimpleGraph V) {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (u v : V) :
    betaT A β u v = betaT A β v u := by
  unfold betaT
  rw [hβ]
  simp only [A.adj_comm]

theorem forestWeight_betaT_star {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) :
    H02.forestWeight (betaT (starA S s₀ hs₀) β) (betaT_symm _ hβ) (starA S s₀ hs₀) = 1 := by
  unfold H02.forestWeight
  refine Finset.prod_eq_one fun e he => ?_
  induction e using Sym2.ind with
  | h u v =>
    have : (starA S s₀ hs₀).Adj u v := by simpa using he
    simp [betaT, this]

theorem mapW_betaT {β : V → V → ℝ} :
    mapW (betaT (starA S s₀ hs₀) β) (collapse S) = mapW β (collapse S) := by
  funext a b
  unfold mapW
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, if_false]
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    have : ¬ (starA S s₀ hs₀).Adj u v := by
      intro h
      obtain ⟨hu', hv'⟩ := starA_mem hs₀ h
      rw [collapse_of_mem hu'] at hu
      rw [collapse_of_mem hv'] at hv
      exact hab (hu.symm.trans hv)
    simp [betaT, this]

theorem quotGraph_star_sup (F0 : SimpleGraph V) :
    quotGraph (collapse S) (starA S s₀ hs₀ ⊔ F0) = edgeQuot (collapse S) F0.edgeFinset := by
  have := quotGraph_sup (collapse S) (starA_hA hs₀) F0.edgeFinset
  rwa [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet] at this

theorem forestWeight_betaT_sup {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) {F0 : SimpleGraph V}
    (hd : Disjoint (starA S s₀ hs₀) F0) :
    H02.forestWeight (betaT (starA S s₀ hs₀) β) (betaT_symm _ hβ) (starA S s₀ hs₀ ⊔ F0) =
      H02.forestWeight β hβ F0 := by
  unfold H02.forestWeight
  have hdisj : Disjoint (starA S s₀ hs₀).edgeFinset F0.edgeFinset := by
    rw [Finset.disjoint_left]
    intro e he he'
    induction e using Sym2.ind with
    | h u v =>
      have h1 : (starA S s₀ hs₀).Adj u v := by simpa using he
      have h2 : F0.Adj u v := by simpa using he'
      exact (_root_.disjoint_iff.1 hd |> fun h => by
        have : (starA S s₀ hs₀ ⊓ F0).Adj u v := ⟨h1, h2⟩
        rw [h] at this; exact this)
  rw [Finset.prod_congr (s₂ := (starA S s₀ hs₀).edgeFinset ∪ F0.edgeFinset)
    (by ext e; simp) (fun _ _ => rfl), Finset.prod_union hdisj]
  have h1 : ∏ e ∈ (starA S s₀ hs₀).edgeFinset,
      Sym2.lift ⟨betaT (starA S s₀ hs₀) β, betaT_symm _ hβ⟩ e = 1 := by
    refine Finset.prod_eq_one fun e he => ?_
    induction e using Sym2.ind with
    | h u v =>
      have : (starA S s₀ hs₀).Adj u v := by simpa using he
      simp [betaT, this]
  rw [h1, one_mul]
  refine Finset.prod_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | h u v =>
    have h2 : F0.Adj u v := by simpa using he
    have : ¬ (starA S s₀ hs₀).Adj u v := fun h1 => by
      have : (starA S s₀ hs₀ ⊓ F0).Adj u v := ⟨h1, h2⟩
      rw [_root_.disjoint_iff.1 hd] at this; exact this
    simp [betaT, this]

/-- **The forest bijection** (weight form): forests of `G` with `S` separated, with the event
`Q` on the quotient forest, versus forests of `G/S`. -/
theorem sum_sep_eq (hs₀ : s₀ ∈ S) {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i)
    (Q : SimpleGraph (Option {v // v ∉ S}) → Prop) :
    ∑ F : SimpleGraph V with F.IsAcyclic ∧ SepS S F ∧ Q (edgeQuot (collapse S) F.edgeFinset),
        H02.forestWeight β hβ F =
      ∑ F' : SimpleGraph (Option {v // v ∉ S}) with F'.IsAcyclic ∧ Q F',
        H02.forestWeight (mapW β (collapse S)) (mapW_symm hβ (collapse S)) F' := by
  have hc := contract_sum_event (collapse S) (starA_isAcyclic hs₀) (starA_hA hs₀)
    (betaT_symm (starA S s₀ hs₀) hβ) Q
  rw [forestWeight_betaT_star hs₀ hβ, one_mul] at hc
  have hR : ∀ F' : SimpleGraph (Option {v // v ∉ S}),
      H02.forestWeight (mapW (betaT (starA S s₀ hs₀) β) (collapse S))
        (mapW_symm (betaT_symm (starA S s₀ hs₀) hβ) (collapse S)) F' =
      H02.forestWeight (mapW β (collapse S)) (mapW_symm hβ (collapse S)) F' := by
    intro F'
    unfold H02.forestWeight
    refine Finset.prod_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | h x y => simp [mapW_betaT hs₀]
  simp only [hR] at hc
  rw [← hc]
  refine Finset.sum_nbij' (fun F0 => starA S s₀ hs₀ ⊔ F0) (fun F => F \ starA S s₀ hs₀)
    ?_ ?_ ?_ ?_ ?_
  · intro F0 hF0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF0 ⊢
    refine ⟨isAcyclic_sup_of_sep hs₀ hF0.1 hF0.2.1, le_sup_left, ?_⟩
    rw [quotGraph_star_sup hs₀]; exact hF0.2.2
  · intro F hF
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF ⊢
    have hsep := sepS_sdiff_of_isAcyclic hs₀ hF.1 hF.2.1
    refine ⟨hF.1.anti sdiff_le, hsep, ?_⟩
    have := quotGraph_star_sup hs₀ (F \ starA S s₀ hs₀)
    rw [sup_sdiff_cancel_right hF.2.1] at this
    rw [← this]; exact hF.2.2
  · intro F0 hF0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF0
    exact (SepS.disjoint_star hs₀ hF0.2.1).sup_sdiff_cancel_left
  · intro F hF
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
    exact sup_sdiff_cancel_right hF.2.1
  · intro F0 hF0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF0
    exact (forestWeight_betaT_sup hs₀ hβ (SepS.disjoint_star hs₀ hF0.2.1)).symm

end

end ArborealDecay.Wiring
